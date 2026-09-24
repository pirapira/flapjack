import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Exact-source PanSem `If` Error parity

The original HOL `panSemScript$evaluate_def` `If` case returns `SOME Error` with
the unchanged state when the condition expression fails to evaluate or does not
produce a word value.  This module checks the corresponding untagged exact-state
equation in `Flapjack.Pancake.Semantics.PanSem` against the direct HOL oracle
`scripts/hol-probes/pan_sem_ite_e2e_probe.out` (`if_nonword_result=SOME Error`,
`if_fail_result=SOME Error`) for both the clocked and the non-clocked evaluators.
-/

namespace Flapjack.Test.PanSemIteErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain (fun _ => false) false

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def exactLegacy (locals : VarName → Option (PanValue Word64)) :
    PanSemEvaluateState Word64 Unit :=
  { structs := []
    functions := []
    locals := locals
    globals := fun _ => none
    memory := exactMemory
    ffi := statefulTestFfiState
    clock := 5
    baseAddress := 0
    topAddress := 100
    bytesInWord := BitVec.ofNat 64 8 }

private def exactState (locals : VarName → Option (PanValue Word64)) :
    PanSemExactState Word64 Unit :=
  { legacy := exactLegacy locals, memoryAccess := exactAccess }

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
    state program

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX (fun _ => none) exactMemory
    statefulTestFfiState program (memoryAccess := memoryAccess)

private def isWordOption (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

/-- Matches an `Error` control result at `clock` whose `x` local is unchanged. -/
private def isErrorKeepingX (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control (.error locals globals _ _), n) =>
      n == clock && isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

private def isErrorKeepingXStepped (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

/-- A non-word condition value (`RStruct []`). -/
private def nonwordConditionProgram : Prog Word64 :=
  .ite (.rStruct []) .skip .skip

/-- A condition whose evaluation fails (unbound local `z`). -/
private def failedConditionProgram : Prog Word64 :=
  .ite (.var .local "z") .skip .skip

private def iteNonwordGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) nonwordConditionProgram)

private def iteFailedGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) failedConditionProgram)

private def iteNonClockedNonwordGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate nonwordConditionProgram
    (memoryAccess := some exactAccess))

private def iteNonClockedFailedGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate failedConditionProgram
    (memoryAccess := some exactAccess))

private def iteErrorGuard : Bool :=
  iteNonwordGuard && iteFailedGuard && iteNonClockedNonwordGuard && iteNonClockedFailedGuard

#guard iteErrorGuard

example :
    panSemEvaluateExactState statefulTestContext statefulTestPrimitive statefulTestHandler
        (exactState localsWordX) (.ite (.rStruct []) .skip .skip) =
      some (.control (.error (exactLegacy localsWordX).locals
        (exactLegacy localsWordX).globals (exactLegacy localsWordX).memory
        (exactLegacy localsWordX).ffi), (exactLegacy localsWordX).clock) :=
  panSemEvaluateExactState_ite_error_of_condition_none statefulTestContext
    statefulTestPrimitive statefulTestHandler _ _ _ _
    (by simp [exactState, exactLegacy, panValueIteConditionValue, evalPanValueExp])

def runChecks : IO Bool := do
  if iteNonwordGuard then
    IO.println "PASS exact-state If non-word condition keeps state and clock"
  else
    IO.println "FAIL exact-state If non-word condition keeps state and clock"
  if iteFailedGuard then
    IO.println "PASS exact-state If failing condition keeps state and clock"
  else
    IO.println "FAIL exact-state If failing condition keeps state and clock"
  if iteNonClockedNonwordGuard then
    IO.println "PASS non-clocked If non-word condition rejected with Error"
  else
    IO.println "FAIL non-clocked If non-word condition rejected with Error"
  if iteNonClockedFailedGuard then
    IO.println "PASS non-clocked If failing condition rejected with Error"
  else
    IO.println "FAIL non-clocked If failing condition rejected with Error"
  pure iteErrorGuard

end Flapjack.Test.PanSemIteErrorExactParity