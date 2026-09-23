import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for Pancake `evaluate_def`

The source oracle is `scripts/hol-probes/pan_sem_e2e_probe.out`, generated
from `panSemScript.sml:556-736`.  Its `return_41`, `return_mul_42`, and
`return_if_13` observations are direct HOL evaluations of
`FST (panSem$evaluate ...)`; the call, memory, and FFI fixtures use the same
source boundary. State-owned Call and DecCall fixtures exercise nonempty code
maps, nested calls, recursive calls, return shapes, and source-clock timeout.

The fixed-width memory oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_load_probe.out`, generated from
`panSemScript.sml:247-265` and the referenced `mem_load_byte_def` /
`mem_load_32_def` equations. It pins aligned success, domain failure,
little-endian reconstruction, and alignment failure.

The explicit-memory store oracle is `scripts/hol-probes/
pan_sem_evaluate_fixed_store_probe.out`, generated from
`panSemScript.sml:300-390` and `evaluate_def` at :589-608. It checks ordinary
word stores, `Store32`, and `StoreByte` through the source memory domain,
including domain/alignment failures and preservation of the other state
components.
-/

namespace Flapjack.Test.PanEvaluateParity

open Flapjack
open Flapjack.RiscV

def emptyPanState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { structs := []
    functions := []
    locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8 }

def evaluateSkip :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.skip : Prog (Word 64))

def evaluateReturn41 :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.return (.const (BitVec.ofNat 64 41)) : Prog (Word 64))

def evaluateSequence :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 1)
    ((.seq .tick (.return (.const (BitVec.ofNat 64 13)))) : Prog (Word 64))

def evaluateTickAtZero :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 0) (.tick : Prog (Word 64))

def idFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def idContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("id", .one)] [] [("id", [("x", .one)])]

def evaluateCall :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    ({ emptyPanState 10 with
        functions := idFunctions
        contracts := some idContracts }
      : PanSemEvaluateState (Word 64) Unit)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog (Word 64))

private abbrev Word64 := Word 64

def emptyPanSourceState (clock : Nat)
    (code : PanSemCodeMap Word64) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := code
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def sourceIdCode : PanSemCodeMap Word64 :=
  [("id", ([ ("x", .one) ], .return (.var .local "x"), .one))]

def sourceRecursiveCode : PanSemCodeMap Word64 :=
  [("f", ([], .decCall "nested" .one "g" []
      (.return (.var .local "nested")), .one)),
    ("g", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceCallSelfCode : PanSemCodeMap Word64 :=
  [("loop", ([], .call none "loop" [], .one))]

def sourceDecCallSelfCode : PanSemCodeMap Word64 :=
  [("loop", ([], .decCall "nested" .one "loop" [] .skip, .one))]

def sourceZeroClockCallCode : PanSemCodeMap Word64 :=
  [("callee", ([], .skip, .one))]

def sourceConstReturnCallCode : PanSemCodeMap Word64 :=
  [("constant", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

def sourceRaiseExceptionCallCode : PanSemCodeMap Word64 :=
  [("raiseE", ([], .raise "E" (.const (BitVec.ofNat 64 7)), .one))]

def evaluateSourceCallId :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceIdCode)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog Word64)

def evaluateSourceCallAssigned :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceIdCode with
        locals := fun name =>
          if name == "answer" then some (.word (BitVec.ofNat 64 3)) else none })
    (.call (some (some (.local, "answer"), none)) "id"
      [.const (BitVec.ofNat 64 7)] : Prog Word64)

def evaluateSourceCallRaisesException :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceRaiseExceptionCallCode with
        exceptionShapes := fun exception =>
          if exception == "E" then some .one else none })
    (.call none "raiseE" [] : Prog Word64)

def evaluateSourceCallHandlesException :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 10 sourceRaiseExceptionCallCode with
        locals := fun name =>
          if name == "caught" then some (.word (BitVec.ofNat 64 0)) else none
        exceptionShapes := fun exception =>
          if exception == "E" then some .one else none })
    (.call (some (none, some ("E", "caught",
      .return (.var .local "caught")))) "raiseE" [] : Prog Word64)

def evaluateSourceDecCallId :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceIdCode)
    (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)]
      (.return (.var .local "answer")) : Prog Word64)

def evaluateSourceNestedCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceRecursiveCode)
    (.call none "f" [] : Prog Word64)

def evaluateSourceNestedCallWithPostState :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8)
    (emptyPanSourceState 10 sourceRecursiveCode)
    (.call none "f" [] : Prog Word64)

def evaluateSourceRecursiveCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 2 sourceCallSelfCode)
    (.call none "loop" [] : Prog Word64)

def evaluateSourceRecursiveDecCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 2 sourceDecCallSelfCode)
    (.decCall "answer" .one "loop" [] .skip : Prog Word64)

def evaluateSourceZeroClockCallTimeout :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    ({ emptyPanSourceState 0 sourceZeroClockCallCode with
        locals := fun name =>
          if name == "x" then some (.word (BitVec.ofNat 64 9)) else none })
    (.call none "callee" [] : Prog Word64)

def evaluateSourceConstReturnCall :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler
    (emptyPanSourceState 10 sourceConstReturnCallCode)
    (.call none "constant" [] : Prog Word64)

private def isSourceReturnedWord
    (result : Option (PanValueFfiClockResult Word64 Unit))
    (expected : Word64) (expectedClock : Nat) : Bool :=
  match result with
  | some (.control (.returned _ _ _ _ [(.word value)]), clock) =>
      value == expected && clock == expectedClock
  | _ => false

private def isSourceTimeoutAt
    (result : Option (PanValueFfiClockResult Word64 Unit))
    (expectedClock : Nat) : Bool :=
  match result with
  | some (.timeout _ _ _ _, clock) => clock == expectedClock
  | _ => false

def observeSourceCodeCall := isSourceReturnedWord evaluateSourceCallId
  (BitVec.ofNat 64 7) 9

def observeSourceCallAssigned : Bool :=
  match evaluateSourceCallAssigned with
  | some (.control (.normal locals _globals _memory _ffi), 9) =>
      match locals "answer" with
      | some (.word value) => value == BitVec.ofNat 64 7
      | _ => false
  | _ => false

def observeSourceCallRaisesException : Bool :=
  match evaluateSourceCallRaisesException with
  | some (.control (.raised _ _ _ _ "E" (.word value)), 9) =>
      value == BitVec.ofNat 64 7
  | _ => false

def observeSourceCallHandlesException : Bool :=
  isSourceReturnedWord evaluateSourceCallHandlesException
    (BitVec.ofNat 64 7) 9

def observeSourceCodeDecCall := isSourceReturnedWord evaluateSourceDecCallId
  (BitVec.ofNat 64 7) 9

def observeSourceNestedCodeCall := isSourceReturnedWord evaluateSourceNestedCall
  (BitVec.ofNat 64 7) 8

def observeSourceCodePreservedAfterRecursion : Bool :=
  match evaluateSourceNestedCallWithPostState with
  | some (_, postState) =>
      match panSemCodeLookup postState.code "f", panSemCodeLookup postState.code "g" with
      | some (_, .decCall "nested" .one "g" [] _, .one),
          some ([], .return (.const value), .one) =>
          value == BitVec.ofNat 64 7
      | _, _ => false
  | none => false

def observeSourceRecursiveCallTimeout :=
  isSourceTimeoutAt evaluateSourceRecursiveCallTimeout 0

def observeSourceRecursiveDecCallTimeout :=
  isSourceTimeoutAt evaluateSourceRecursiveDecCallTimeout 0

def observeSourceZeroClockCallTimeout : Bool :=
  match evaluateSourceZeroClockCallTimeout with
  | some (.timeout locals _ _ _, 0) =>
      match locals "x" with
      | none => true
      | some _ => false
  | _ => false

def observeSourceConstReturnCall := isSourceReturnedWord
  evaluateSourceConstReturnCall (BitVec.ofNat 64 7) 9

#guard observeSourceCodeCall
#guard observeSourceCallAssigned
#guard observeSourceCallRaisesException
#guard observeSourceCallHandlesException
#guard observeSourceCodeDecCall
#guard observeSourceNestedCodeCall
#guard observeSourceCodePreservedAfterRecursion
#guard observeSourceRecursiveCallTimeout
#guard observeSourceRecursiveDecCallTimeout
#guard observeSourceZeroClockCallTimeout
#guard observeSourceConstReturnCall

/-! The fixed-width branches must go through the explicit source memory model.
    This is the stateful evaluator path corresponding to
    `panSemScript.sml:247-265`, not the legacy whole-cell fallback. -/
def fixedLoadDomain : PanMemoryDomain (Word 64) :=
  fun address => address == BitVec.ofNat 64 8

def fixedLoadMemory : Word 64 → Option (PanValue (Word 64)) :=
  fun address =>
    if address == BitVec.ofNat 64 8 then
      some (.word (BitVec.ofNat 64 0x0807060504030201))
    else none

def fixedLoadAccess : PanValueMemoryAccess (Word 64) :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel fixedLoadDomain

def evaluateExactProgramWord32 :=
  evalPanValueProgExact [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none) fixedLoadMemory fixedLoadAccess
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

def evaluateExactProgramByteDomainFailure :=
  evalPanValueProgExact [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) (fun _ => none) (fun _ => none) fixedLoadMemory fixedLoadAccess
    (.return (.loadByte (.const (BitVec.ofNat 64 16))) : Prog (Word 64))

def fixedLoadState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { emptyPanState clock with
      memory := fixedLoadMemory
      memoryAccess := some fixedLoadAccess }

def fixedLoadStateWithoutAccess (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { fixedLoadState clock with memoryAccess := none }

def fixedExactState : PanSemExactState (Word 64) Unit :=
  { legacy := fixedLoadStateWithoutAccess 4
    memoryAccess := fixedLoadAccess }

def nestedRaiseExpression : Exp (Word 64) :=
  .rStruct [.const (BitVec.ofNat 64 3),
    .rStruct [.const (BitVec.ofNat 64 4), .const (BitVec.ofNat 64 5)]]

def evaluateNestedRaise :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler fixedExactState
    (.raise "E" nestedRaiseExpression : Prog (Word 64))

def fixedStoreLocals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "kept" then some (.word (BitVec.ofNat 64 55)) else none

def fixedStoreGlobals : VarName → Option (PanValue (Word 64)) :=
  fun name => if name == "keptGlobal" then some (.word (BitVec.ofNat 64 66)) else none

def fixedStoreState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { fixedLoadState clock with
      locals := fixedStoreLocals
      globals := fixedStoreGlobals }

def evaluateFixedByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 9))) : Prog (Word 64))

def evaluateFixedWord32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

example :
    panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
        fixedLoadAccess (fixedLoadStateWithoutAccess 4)
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) =
      panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
        { fixedLoadStateWithoutAccess 4 with memoryAccess := some fixedLoadAccess }
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) := by
  exact panSemEvaluateExact_uses_memory_access
    statefulTestContext statefulTestPrimitive statefulTestHandler fixedLoadAccess
    (fixedLoadStateWithoutAccess 4)
    (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64))

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive
        statefulTestHandler fixedExactState
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) =
      panSemEvaluateExact statefulTestContext statefulTestPrimitive
        statefulTestHandler fixedLoadAccess (fixedLoadStateWithoutAccess 4)
        (.return (.load32 (.const (BitVec.ofNat 64 8))) : Prog (Word 64)) := by
  rfl

def evaluateFixedByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedLoadState 4)
    (.return (.loadByte (.const (BitVec.ofNat 64 16))) : Prog (Word 64))

def evaluateFixedStore :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStoreDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0x1122334455667788)) : Prog (Word 64))

def evaluateFixedStore32 :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStore32Unaligned :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.store32 (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0x11223344)) : Prog (Word 64))

def evaluateFixedStoreByte :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 9))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def evaluateFixedStoreByteDomainFailure :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 4)
    (.storeByte (.const (BitVec.ofNat 64 16))
      (.const (BitVec.ofNat 64 0xaa)) : Prog (Word 64))

def emptySharedContext : PanValueFfiContext (Word 64) :=
  { statefulTestContext with sharedDomain := fun _ => false }

def evaluateIfBadCondition :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.ite (.var .local "missing") .skip .skip : Prog (Word 64))

def evaluateIfOk :=
  panSemEvaluateExact statefulTestContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.ite (.const (BitVec.ofNat 64 1)) .skip .skip : Prog (Word 64))

def evaluateShMemLoadUnbound :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemLoad .op8 .local "missing" (.const (BitVec.ofNat 64 8)) : Prog (Word 64))

def evaluateShMemLoadDomainFailure :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemLoad .op8 .local "kept" (.const (BitVec.ofNat 64 8)) : Prog (Word 64))

def evaluateShMemStoreDomainFailure :=
  panSemEvaluateExact emptySharedContext statefulTestPrimitive statefulTestHandler
    fixedLoadAccess (fixedStoreState 5)
    (.shMemStore .op8 (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 7)) : Prog (Word 64))

def isWord (expected : Nat) : PanValue (Word 64) → Bool
  | .word value => value == BitVec.ofNat 64 expected
  | _ => false

def observeSkip : Bool :=
  match evaluateSkip with
  | some (.control (.normal locals _ _ _), 4) => locals "x" = none
  | _ => false

def observeReturn41 : Bool :=
  match evaluateReturn41 with
  | some (.control (.returned locals _ _ _ [value]), 4) =>
      locals "x" = none && isWord 41 value
  | _ => false

def observeSequence : Bool :=
  match evaluateSequence with
  | some (.control (.returned _ _ _ _ [value]), 0) => isWord 13 value
  | _ => false

def observeTickAtZero : Bool :=
  match evaluateTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

def observeCall : Bool :=
  match evaluateCall with
  | some (.control (.returned locals _ _ _ [value]), 9) =>
      locals "x" = none && isWord 7 value
  | _ => false

def observeNestedRaise : Bool :=
  match evaluateNestedRaise with
  | some (.control (.raised locals _ _ _ "E"
      (.rStruct [.word first, .rStruct [.word second, .word third]])), 4) =>
      locals "x" = none &&
        first == BitVec.ofNat 64 3 &&
        second == BitVec.ofNat 64 4 &&
        third == BitVec.ofNat 64 5
  | _ => false

def isErrorResult {α σ : Type} : Option (PanValueFfiClockResult α σ) → Bool
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

def observeFixedLoads : Bool :=
  match evaluateFixedByte, evaluateFixedWord32 with
  | some (.control (.returned _ _ _ _ [(.word byte)]), 4),
      some (.control (.returned _ _ _ _ [(.word word32)]), 4) =>
      byte == BitVec.ofNat 64 2 && word32 == BitVec.ofNat 64 0x04030201
  | _, _ => false

def observeFixedLoadDomainFailure : Bool :=
  isErrorResult evaluateFixedByteDomainFailure

def observeExactProgramMemoryAccess : Bool :=
  match evaluateExactProgramWord32 with
  | some (_, _, _, [(.word value)]) =>
      value == BitVec.ofNat 64 0x04030201
  | _ => false

def observeExactProgramDomainFailure : Bool :=
  evaluateExactProgramByteDomainFailure.isNone

def isWordOption (expected : Nat) : Option (PanValue (Word 64)) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

def isNoneOption : Option (PanValue (Word 64)) → Bool
  | none => true
  | _ => false

def observeFixedStore : Bool :=
  match evaluateFixedStore with
  | some (.control (.normal locals globals memory ffi), 4) =>
      isWordOption 55 (locals "kept") &&
      isWordOption 66 (globals "keptGlobal") &&
      isWordOption 0x1122334455667788 (memory (BitVec.ofNat 64 8)) &&
      isNoneOption (memory (BitVec.ofNat 64 16)) &&
      decide (ffi.ioEvents = statefulTestFfiState.ioEvents)
  | _ => false

def observeFixedStore32 : Bool :=
  match evaluateFixedStore32 with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x0807060511223344 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreByte : Bool :=
  match evaluateFixedStoreByte with
  | some (.control (.normal _ _ memory _), 4) =>
      isWordOption 0x080706050403aa01 (memory (BitVec.ofNat 64 8))
  | _ => false

def observeFixedStoreFailures : Bool :=
  isErrorResult evaluateFixedStoreDomainFailure &&
    isErrorResult evaluateFixedStore32Unaligned &&
    isErrorResult evaluateFixedStoreByteDomainFailure

def errorPreservingKeptAt (clock localValue : Nat) :
    Option (PanValueFfiClockResult (Word 64) Unit) → Bool
  | some (.control (.error locals _ _ _), n) =>
      n == clock && isWordOption localValue (locals "kept")
  | _ => false

def observeIfBadCondition : Bool :=
  errorPreservingKeptAt 5 55 evaluateIfBadCondition

def observeIfOk : Bool :=
  match evaluateIfOk with
  | some (.control (.normal locals _ _ _), 5) => isWordOption 55 (locals "kept")
  | _ => false

def observeShMemLoadUnbound : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemLoadUnbound

def observeShMemLoadDomainFailure : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemLoadDomainFailure

def observeShMemStoreDomainFailure : Bool :=
  errorPreservingKeptAt 5 55 evaluateShMemStoreDomainFailure

#guard observeSkip
#guard observeReturn41
#guard observeSequence
#guard observeTickAtZero
#guard observeCall
#guard observeNestedRaise
#guard observeFixedLoads
#guard observeFixedLoadDomainFailure
#guard observeExactProgramMemoryAccess
#guard observeExactProgramDomainFailure
#guard observeFixedStore
#guard observeFixedStore32
#guard observeFixedStoreByte
#guard observeFixedStoreFailures
#guard observeIfBadCondition
#guard observeIfOk
#guard observeShMemLoadUnbound
#guard observeShMemLoadDomainFailure
#guard observeShMemStoreDomainFailure

def runChecks : IO Bool := do
  if observeSkip then IO.println "PASS evaluate skip" else IO.println "FAIL evaluate skip"
  if observeReturn41 then IO.println "PASS evaluate return_41" else IO.println "FAIL evaluate return_41"
  if observeSequence then IO.println "PASS evaluate sequence" else IO.println "FAIL evaluate sequence"
  if observeTickAtZero then IO.println "PASS evaluate timeout" else IO.println "FAIL evaluate timeout"
  if observeCall then IO.println "PASS evaluate call_id_7" else IO.println "FAIL evaluate call_id_7"
  if observeSourceCodeCall then IO.println "PASS state-owned code Call matches HOL call_code_map_7" else
    IO.println "FAIL state-owned code Call matches HOL call_code_map_7"
  if observeSourceCallAssigned then IO.println "PASS state-owned Call writes the existing local destination" else
    IO.println "FAIL state-owned Call writes the existing local destination"
  if observeSourceCallRaisesException then IO.println "PASS state-owned Call propagates the callee exception payload" else
    IO.println "FAIL state-owned Call propagates the callee exception payload"
  if observeSourceCallHandlesException then IO.println "PASS state-owned Call handler catches and binds the exception payload" else
    IO.println "FAIL state-owned Call handler catches and binds the exception payload"
  if observeSourceCodeDecCall then IO.println "PASS state-owned code DecCall matches HOL deccall_code_map_7" else
    IO.println "FAIL state-owned code DecCall matches HOL deccall_code_map_7"
  if observeSourceNestedCodeCall then IO.println "PASS state-owned nested Call and DecCall match HOL recursive oracle" else
    IO.println "FAIL state-owned nested Call and DecCall match HOL recursive oracle"
  if observeSourceCodePreservedAfterRecursion then IO.println "PASS recursive code-map evaluation preserves source code" else
    IO.println "FAIL recursive code-map evaluation preserves source code"
  if observeSourceRecursiveCallTimeout then IO.println "PASS recursive state-owned Call times out at source clock zero" else
    IO.println "FAIL recursive state-owned Call times out at source clock zero"
  if observeSourceRecursiveDecCallTimeout then IO.println "PASS recursive state-owned DecCall times out at source clock zero" else
    IO.println "FAIL recursive state-owned DecCall times out at source clock zero"
  if observeSourceZeroClockCallTimeout then IO.println "PASS state-owned Call with a nonempty code map times out at zero clock and clears locals" else
    IO.println "FAIL state-owned Call with a nonempty code map times out at zero clock and clears locals"
  if observeSourceConstReturnCall then IO.println "PASS zero-argument state-owned Call returns its code-map word constant" else
    IO.println "FAIL zero-argument state-owned Call returns its code-map word constant"
  if observeNestedRaise then IO.println "PASS evaluate nested structured raise" else
    IO.println "FAIL evaluate nested structured raise"
  if observeFixedLoads then IO.println "PASS evaluate fixed-width loads" else
    IO.println "FAIL evaluate fixed-width loads"
  if observeFixedLoadDomainFailure then IO.println "PASS evaluate fixed-width domain failure" else
    IO.println "FAIL evaluate fixed-width domain failure"
  if observeExactProgramMemoryAccess then IO.println "PASS exact structured program memory access" else
    IO.println "FAIL exact structured program memory access"
  if observeExactProgramDomainFailure then IO.println "PASS exact structured program domain failure" else
    IO.println "FAIL exact structured program domain failure"
  if observeFixedStore then IO.println "PASS evaluate explicit word store" else
    IO.println "FAIL evaluate explicit word store"
  if observeFixedStore32 then IO.println "PASS evaluate explicit Store32" else
    IO.println "FAIL evaluate explicit Store32"
  if observeFixedStoreByte then IO.println "PASS evaluate explicit StoreByte" else
    IO.println "FAIL evaluate explicit StoreByte"
  if observeFixedStoreFailures then IO.println "PASS evaluate explicit store failures" else
    IO.println "FAIL evaluate explicit store failures"
  if observeIfBadCondition then IO.println "PASS evaluate If rejects non-word condition with Error" else
    IO.println "FAIL evaluate If rejects non-word condition with Error"
  if observeIfOk then IO.println "PASS evaluate If word condition keeps clock" else
    IO.println "FAIL evaluate If word condition keeps clock"
  if observeShMemLoadUnbound then IO.println "PASS evaluate ShMemLoad rejects unbound local with Error" else
    IO.println "FAIL evaluate ShMemLoad rejects unbound local with Error"
  if observeShMemLoadDomainFailure then IO.println "PASS evaluate ShMemLoad rejects shared-domain miss with Error" else
    IO.println "FAIL evaluate ShMemLoad rejects shared-domain miss with Error"
  if observeShMemStoreDomainFailure then IO.println "PASS evaluate ShMemStore rejects shared-domain miss with Error" else
    IO.println "FAIL evaluate ShMemStore rejects shared-domain miss with Error"
  pure (observeSkip && observeReturn41 && observeSequence && observeTickAtZero && observeCall &&
    observeSourceCodeCall && observeSourceCodeDecCall && observeSourceNestedCodeCall &&
    observeSourceCodePreservedAfterRecursion &&
    observeSourceRecursiveCallTimeout && observeSourceRecursiveDecCallTimeout &&
    observeSourceZeroClockCallTimeout && observeSourceConstReturnCall &&
    observeNestedRaise &&
    observeFixedLoads && observeFixedLoadDomainFailure &&
    observeExactProgramMemoryAccess && observeExactProgramDomainFailure &&
    observeFixedStore &&
    observeFixedStore32 && observeFixedStoreByte && observeFixedStoreFailures &&
    observeIfBadCondition && observeIfOk && observeShMemLoadUnbound &&
    observeShMemLoadDomainFailure && observeShMemStoreDomainFailure)

end Flapjack.Test.PanEvaluateParity
