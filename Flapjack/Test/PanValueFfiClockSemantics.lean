import Flapjack.PanValueFfiClockSemantics
import Flapjack.PanValueFfiClockProjection
import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.Test.PanValueFfiSemantics

/-! Executable regressions for the CakeML clock boundary. -/

namespace Flapjack

open RiscV

def clockedCallFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("returnOne", [], .return (.const (BitVec.ofNat 64 1)))]

def clockedBreakProgram : Prog (Word 64) :=
  .while (.const (BitVec.ofNat 64 1)) .break

def clockedTickAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 0 .tick

def clockedTickAtOne :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 1 .tick

def clockedBreak :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 1 clockedBreakProgram

def clockedCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    none "returnOne" []

def clockedProgramCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "returnOne" [])

def clockedProgramCallDestination :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun name => if name == "x" then some (.word (BitVec.ofNat 64 0)) else none)
    (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call (some (some (.local, "x"), none)) "returnOne" [])

def clockedCallAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 0
    none "returnOne" []

def clockedTimeoutFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("timeoutLoop", [], .while (.const (BitVec.ofNat 64 1)) .skip)]

def clockedCallBodyTimeout : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedTimeoutFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    none "timeoutLoop" []

def clockedProgramBodyTimeout : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedTimeoutFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "timeoutLoop" [])

def clockedDecCallAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 0
    (.decCall "x" .one "returnOne" [] .skip)

def clockedDecCallReturned : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.decCall "x" .one "returnOne" []
      (.return (.var .local "x")))

def clockedRaiseFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("raiseOne", [], .raise "E" (.const (BitVec.ofNat 64 1)))]

def clockedProgramRaisedCall :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call none "raiseOne" [])

def clockedDecCallRaised : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.decCall "x" .one "raiseOne" [] .skip)

def clockedCaughtCall : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (some (none, some ("E", "exceptionValue",
      .return (.var .local "exceptionValue")))) "raiseOne" []

def clockedProgramCaughtCall : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedRaiseFunctions 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 1
    (.call (some (none, some ("E", "exceptionValue",
      .return (.var .local "exceptionValue")))) "raiseOne" [])

def clockedInvalidCallTerminal :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [("skip", [], .skip)] 0 100 8 20
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState 5
    none "skip" []

def clockedFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFinalState 10
    ((.dec "x" .one (.const (BitVec.ofNat 64 0))
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))) : Prog (Word 64))

def clockedDirectExtCallFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] []
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState 10
    (.extCall "final" (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)))
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def clockedCallFinalFfiFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("finalExt", [],
    .extCall "final" (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)))]

def clockedCallFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState 10 (.call none "finalExt" [])
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

def clockedCallFinalFfiSteps : Option (PanValueFfiSteppedResult (Word 64) Unit) :=
  evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState none "finalExt" []
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

/- CakeML's `panSem.evaluate_def` handles `If` by evaluating a word-valued
   condition and selecting the nonzero branch (panSemScript.sml:618-621).
   This exact structured evaluator guard also exercises the ordinary memory
   load used by that equation; the removed compact evaluator had no source
   semantics or shape checks. -/
def exactMemoryBranch : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    statefulTestMemory statefulTestFfiState 1
    (.ite (.cmp .equal (.load .one (.const (BitVec.ofNat 64 8)))
      (.const (BitVec.ofNat 64 0x42)))
      (.return (.const (BitVec.ofNat 64 1)))
      (.return (.const (BitVec.ofNat 64 0))))
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

#guard
  match exactMemoryBranch with
  | some (.control (.returned _ _ _ _ [PanValue.word value]), 1) =>
      value == BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCallFinalFfi with
  | some (.control (.finalFfi locals _ _ _ event), 9) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedCallFinalFfiSteps with
  | some (.finalFfi locals _ _ _ event, _) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedTickAtOne with
  | some (.control (.normal _ _ _ _), 0) => true
  | _ => false

#guard
  match clockedBreak with
  | some (.control (.normal _ _ _ _), 0) => true
  | _ => false

#guard
  match clockedCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCallDestination with
  | some (.control (.normal locals _ _ _), 0) =>
      match locals "x" with
      | some (.word value) => value == BitVec.ofNat 64 1
      | _ => false
  | _ => false

#guard
  match clockedProgramRaisedCall with
  | some (.control (.raised locals _ _ _ "E" (PanValue.word value)), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedDecCallRaised with
  | some (.control (.raised locals _ _ _ "E" (PanValue.word value)), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCallAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedCallBodyTimeout with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedProgramBodyTimeout with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedDecCallAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

#guard
  match clockedDecCallReturned with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "x" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedCaughtCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "exceptionValue" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard
  match clockedProgramCaughtCall with
  | some (.control (.returned locals _ _ _ [PanValue.word value]), 0) =>
      locals "exceptionValue" = none && value = BitVec.ofNat 64 1
  | _ => false

#guard clockedInvalidCallTerminal.isNone

/- The named result projection keeps the exact source state and remaining
   clock while making timeout and terminal FFI outcomes distinct. -/
#guard
  match clockedTickAtZero.map panValueFfiClockResultProjection with
  | some (.timeout locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedTickAtOne.map panValueFfiClockResultProjection with
  | some (.normal locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedFinalFfi.map panValueFfiClockResultProjection with
  | some (.finalFfi locals globals memory ffi event 10) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = () && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed
  | _ => false

#guard
  match clockedDirectExtCallFinalFfi with
  | some (.control (.finalFfi locals _ _ _ event), 10) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

/-! A `DecCall` whose callee terminates the host reaches the same terminal FFI
    outcome as the direct `ExtCall` above.  The regression instantiates the Pc
    result lift for that branch: the callee evaluation is an explicit premise,
    and the source state relation is discharged from the flat source state. -/
def clockedPcContext : CompileContext (Word 64) :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := BitVec.ofNat 64 8 }

example (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler [] clockedCallFinalFfiFunctions
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 9
      (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
      10 none "finalExt" [] =
      some (.control (.finalFfi (fun _ => none) (fun _ => none)
        statefulTestMemory statefulTestFinalState event), 9)) :
    panValuePcResultRel [] clockedPcContext (fun _ _ _ => True)
      (fun _ => none) (fun _ _ => none)
      (.finalFfi (fun _ => none) (fun _ => none) statefulTestMemory event)
      (.finalFfi { locals := fun _ => none, memory := panValueWordMemory statefulTestMemory, globals := fun _ => none } event) :=
  (panValuePcFinalFfiResultRel_of_clocked_decCall [] clockedPcContext
    (fun _ _ _ => True) (fun _ => none) (fun _ _ => none)
    statefulTestContext statefulTestPrimitive statefulTestHandler
    clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 9 10 9
    (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
    "x" .one "finalExt" [] .skip
    (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
    event event
    { locals := fun _ => none, memory := panValueWordMemory statefulTestMemory, globals := fun _ => none }
    hcall (by
      constructor
      · rfl
      · constructor
        · intro name value shape slots h
          cases h
        · rfl) rfl).2.2

/-! The direct `Call` branch reaches the same terminal FFI outcome without a
    declaration continuation; the same explicit callee evaluation and flat
    source state discharge the Pc result lift for that branch. -/
example (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall statefulTestContext statefulTestPrimitive
      statefulTestHandler [] clockedCallFinalFfiFunctions
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 9
      (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
      10 none "finalExt" [] =
      some (.control (.finalFfi (fun _ => none) (fun _ => none)
        statefulTestMemory statefulTestFinalState event), 9)) :
    panValuePcResultRel [] clockedPcContext (fun _ _ _ => True)
      (fun _ => none) (fun _ _ => none)
      (.finalFfi (fun _ => none) (fun _ => none) statefulTestMemory event)
      (.finalFfi { locals := fun _ => none, memory := panValueWordMemory statefulTestMemory, globals := fun _ => none } event) :=
  (panValuePcFinalFfiResultRel_of_clocked_call [] clockedPcContext
    (fun _ _ _ => True) (fun _ => none) (fun _ _ => none)
    statefulTestContext statefulTestPrimitive statefulTestHandler
    clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 9 10 9
    (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
    none "finalExt" []
    (fun _ => none) (fun _ => none) statefulTestMemory statefulTestFinalState
    event event
    { locals := fun _ => none, memory := panValueWordMemory statefulTestMemory, globals := fun _ => none }
    hcall (by
      constructor
      · rfl
      · constructor
        · intro name value shape slots h
          cases h
        · rfl) rfl).2.2

end Flapjack
