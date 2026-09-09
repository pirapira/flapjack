import Flapjack.PanValueFfiSemantics
import Flapjack.RiscV.PanMemory

/-!
Executable checks for the stateful structured source evaluator.  The oracle
returns a fixed word for shared reads and echoes write payloads, which makes
both the `SharedMem` event and the stepped result observable.
-/

namespace Flapjack

open RiscV

def statefulTestDecodeLittleEndian : List UInt8 → Nat → Nat
  | [], _ => 0
  | byte :: bytes, index => byte.toNat * 256 ^ index +
      statefulTestDecodeLittleEndian bytes (index + 1)

def statefulTestWordToBytes (value : Word 64) (bigEndian : Bool) : List UInt8 :=
  let bytes := (List.range 8).map (fun index =>
    UInt8.ofNat ((value.toNat / 256 ^ index) % 256))
  if bigEndian then bytes.reverse else bytes

def statefulTestWordOfBytes (bigEndian : Bool) (bytes : List UInt8) : Word 64 :=
  let bytes := if bigEndian then bytes.reverse else bytes
  BitVec.ofNat 64 (statefulTestDecodeLittleEndian bytes 0)

def statefulTestOracle : FfiOracle Unit :=
  fun name state _ bytes =>
    match name with
    | .sharedMem .mappedRead =>
        .returned state (statefulTestWordToBytes (BitVec.ofNat 64 0x42) false)
    | .sharedMem .mappedWrite => .returned state bytes
    | .extCall _ => .returned state bytes

def statefulTestFfiState : FfiState Unit :=
  { oracle := statefulTestOracle, state := (), ioEvents := [] }

def statefulTestContext : PanValueFfiContext (Word 64) :=
  { sharedDomain := fun _ => true
    byteAlign := fun address => panRiscVByteAlign (BitVec.ofNat 64 8) address
    bigEndian := false
    wordToBytes := statefulTestWordToBytes
    wordOfBytes := statefulTestWordOfBytes
    wordToByte := fun value => UInt8.ofNat value.toNat
    byteToWord := fun value => BitVec.ofNat 64 value.toNat
    valueToNat := fun value => value.toNat }

def statefulTestHandler : PanValueStatefulFfiHandler (Word 64) Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def statefulTestPrimitive : PanPrimitiveHandler (Word 64) :=
  fun _ _ => none

#guard panValuePayloadWithinLimit []
  (.rStruct [.word (BitVec.ofNat 64 1), .word (BitVec.ofNat 64 2)])

def statefulTestMemory : Word 64 → Option (PanValue (Word 64)) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x0000000000000042))
    else none

def statefulExtCallWriteFailureAccess : PanValueMemoryAccess (Word 64) :=
  { panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel with
    readByte := fun _ _ _ _ => some 0
    storeByte := fun _ memory _ address value =>
      if address == BitVec.ofNat 64 8 then
        some (fun current =>
          if current == address then some (.word value) else memory current)
      else none }

def statefulExtCallWriteFailureOracle : FfiOracle Unit :=
  fun name state _ _ =>
    match name with
    | .extCall _ => .returned state [UInt8.ofNat 1, UInt8.ofNat 2]
    | _ => .returned state []

def statefulExtCallWriteFailureFfi : FfiState Unit :=
  { oracle := statefulExtCallWriteFailureOracle, state := (), ioEvents := [] }

#guard
  match panValueFfiExtCall statefulExtCallWriteFailureAccess statefulTestContext
      (fun address =>
        if address == BitVec.ofNat 64 8 then some (.word 0) else none)
      (BitVec.ofNat 64 8) statefulExtCallWriteFailureFfi "writeFailure"
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 2) with
  | some (.returned memory _) =>
      (match memory (BitVec.ofNat 64 8) with
        | some (.word value) => value == BitVec.ofNat 64 1
        | _ => false) &&
        (memory (BitVec.ofNat 64 9)).isNone
  | _ => false

def statefulSharedProgram : Option (Word 64 × Nat × Nat) :=
  (evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 30 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFfiState
      (.dec "x" .one (.const (BitVec.ofNat 64 0))
        (.seq (.shMemStore .op8 (.const (BitVec.ofNat 64 9))
            (.const (BitVec.ofNat 64 0xaa)))
          (.seq (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))
            (.return (.var .local "x")))))).map
    fun result => match result.1 with
      | .returned _ _ _ ffi [.word value] => (value, result.2, ffi.ioEvents.length)
      | _ => (BitVec.ofNat 64 0, 0, 0)

def statefulTestFinalOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .failed

def statefulTestFinalState : FfiState Unit :=
  { oracle := statefulTestFinalOracle, state := (), ioEvents := [] }

def statefulSharedFinalResult :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFinalState
      (.dec "x" .one (.const (BitVec.ofNat 64 0))
        (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10))))

def statefulSharedFinal : Bool :=
  match statefulSharedFinalResult with
  | some (.finalFfi locals _ _ _ event, steps) =>
      locals "x" = none && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed && steps = 4
  | _ => false

#guard statefulSharedProgram = some (BitVec.ofNat 64 0x42, 11, 2)
#guard statefulSharedFinal

/- CakeML's final shared-store outcome preserves the current locals, unlike
   the final shared-load and ExtCall boundaries which clear them. -/
def statefulSharedStoreFinalResult :=
  evalPanValueFfiProgSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10
      (fun name =>
        if name == "x" then some (.word (BitVec.ofNat 64 0)) else none)
      (fun _ => none) (fun _ => none) statefulTestFinalState
      (.shMemStore .op8 (.const (BitVec.ofNat 64 10))
        (.const (BitVec.ofNat 64 0xaa)))

def statefulSharedStoreFinal : Bool :=
  match statefulSharedStoreFinalResult with
  | some (.finalFfi locals _ _ _ event, steps) =>
        (match locals "x" with
       | some (.word value) => value == BitVec.ofNat 64 0
       | _ => false) &&
        event.name == .sharedMem .mappedWrite &&
        event.outcome == .failed && steps == 3
  | _ => false

#guard statefulSharedStoreFinal

#guard
  (evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
      statefulTestFfiState
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))).isNone

def statefulNormalCallRejected : Bool :=
  (evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skip", [], .skip)] (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 10
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState none
    "skip" []).isNone

#guard statefulNormalCallRejected

def statefulExtCallProgram : Option (Word 64 × Nat × Nat) :=
  (evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
      statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
      (BitVec.ofNat 64 8) 30 (fun _ => none) (fun _ => none) statefulTestMemory
      statefulTestFfiState
      (.seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 1)))
        (.return (.loadByte (.const (BitVec.ofNat 64 8)))))
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).map
    fun result => match result.1 with
      | .returned _ _ _ ffi [.word value] => (value, result.2, ffi.ioEvents.length)
      | _ => (BitVec.ofNat 64 0, 0, 0)

#guard statefulExtCallProgram = some (BitVec.ofNat 64 0x42, 9, 1)

def statefulPublicProgramState : PanValueFfiProgramState (Word 64) Unit :=
  { source :=
      { structs := []
        globals := fun _ => none
        functions := []
        returnShapes := []
        exceptions := []
        memory := statefulTestMemory
        baseAddress := BitVec.ofNat 64 0
        topAddress := BitVec.ofNat 64 100
        bytesInWord := BitVec.ofNat 64 8 }
    ffi := statefulTestFfiState }

def statefulOversizedValues : Exp (Word 64) :=
  .rStruct (List.replicate 33 (.const (BitVec.ofNat 64 1)))

def statefulOversizedShape : Shape :=
  .comb (List.replicate 33 .one)

#guard
  (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
    statefulTestPrimitive statefulTestHandler 30
    [.function
       { name := "oversized", inline := false, exported := true, params := [],
         body := .return statefulOversizedValues,
         returnShape := statefulOversizedShape }]
    "oversized" []).isNone

#guard
  (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
    statefulTestPrimitive statefulTestHandler 30
    [.exnDecl "Oversized" statefulOversizedShape,
     .function
       { name := "raisesOversized", inline := false, exported := true, params := [],
         body := .raise "Oversized" statefulOversizedValues,
         returnShape := .one }]
    "raisesOversized" []).isNone

def statefulPublicProgram : Option (Word 64 × Nat) :=
  (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
        { name := "main", inline := false, exported := true, params := [],
          body := .seq (.extCall "echo" (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
              (.const (BitVec.ofNat 64 1)))
            (.return (.loadByte (.const (BitVec.ofNat 64 8)))),
          returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).bind
    fun result => match result with
      | .returned _ _ _ ffi [.word value] => some (value, ffi.ioEvents.length)
      | _ => none

#guard statefulPublicProgram = some (BitVec.ofNat 64 0x42, 1)

example :
    (evalPanValueFfiProgramStepped statefulTestContext
      statefulPublicProgramState statefulTestPrimitive statefulTestHandler
      30 [] "missing" []).map Prod.fst =
      evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
        statefulTestPrimitive statefulTestHandler 30 [] "missing" [] := by
  apply evalPanValueFfiProgramStepped_fst

#guard
    (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.function
         { name := "badReturn", inline := false, exported := false, params := [],
           body := .return (.rStruct [.const (BitVec.ofNat 64 1),
             .const (BitVec.ofNat 64 2)]), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badReturn" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).isNone =
      true

#guard
    (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 30
      [.exnDecl "E" (.comb [.one, .one]),
       .function
         { name := "badRaise", inline := false, exported := false, params := [],
           body := .raise "E" (.const (BitVec.ofNat 64 1)), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badRaise" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).isNone =
      true

#guard
    (evalPanValueFfiProgram statefulTestContext statefulPublicProgramState
      statefulTestPrimitive statefulTestHandler 40
      [.exnDecl "E" .one,
       .function
         { name := "raiseGood", inline := false, exported := false, params := [],
           body := .raise "E" (.const (BitVec.ofNat 64 1)), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq
             (.dec "caught" .one (.const 0)
               (.call (some (none, some ("E", "missing", .skip)))
                 "raiseGood" []))
             (.return (.const 0)), returnShape := .one }]
      "main" []
      (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))).isNone =
      true

end Flapjack
