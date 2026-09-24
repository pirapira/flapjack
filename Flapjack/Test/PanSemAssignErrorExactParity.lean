import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
Direct regression for the exact source `PanSemExactState` `Assign` error
equations.  HOL `panSemScript.sml:566-574` rejects an `Assign` whose source
expression fails to evaluate and one whose destination fails `is_valid_value`,
both with `SOME Error` over the unchanged state.

The expected values reuse the original-HOL `EVAL` rows:

* `scripts/hol-probes/pan_sem_assign_e2e_probe.out`:
  `assign_fresh_invalid_result=SOME Error`,
  `assign_eval_missing_result=SOME Error`;
* `scripts/hol-probes/pan_sem_assign_memory_probe.out`:
  `assign_mem_domain_result=SOME Error`,
  `assign_mem_domain_locals=SOME (ValWord 3w)`,
  `assign_mem_domain_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemAssignErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false

private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun _ => some (.word 0)

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
    bytesInWord := 8
    memoryAccess := none }

private def exactState (locals : VarName → Option (PanValue Word64)) :
    PanSemExactState Word64 Unit :=
  { legacy := exactLegacy locals, memoryAccess := exactAccess }

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

/-- Error at `clock` whose preserved `"x"` local is the given word and whose
globals stay empty. -/
private def isErrorKeepingX (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals globals _ _ =>
          n == clock &&
            (match locals "x" with
             | some (.word word) => word == BitVec.ofNat 64 value
             | _ => false) &&
            (globals "g").isNone
      | _ => false
  | _ => false

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX
    (fun _ => none) exactMemory statefulTestFfiState program
    (memoryAccess := memoryAccess)

private def isErrorSteppedKeepingX (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      (match locals "x" with
       | some (.word word) => word == BitVec.ofNat 64 value
       | _ => false) &&
        (globals "g").isNone
  | _ => false

private def assignLocalEvalFailProgram : Prog Word64 :=
  .assign .local "x" (.var .local "z")

private def assignGlobalEvalFailProgram : Prog Word64 :=
  .assign .global "x" (.var .local "z")

private def assignFreshLocalProgram : Prog Word64 :=
  .assign .local "y" (.const 9)

private def assignFreshGlobalProgram : Prog Word64 :=
  .assign .global "y" (.const 9)

private def assignLocalEvalFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) assignLocalEvalFailProgram)

private def assignGlobalEvalFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) assignGlobalEvalFailProgram)

private def assignFreshLocalGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) assignFreshLocalProgram)

private def assignFreshGlobalGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (exactState localsWordX) assignFreshGlobalProgram)

private def assignNonClockedEvalFailGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignLocalEvalFailProgram
    (memoryAccess := some exactAccess))

private def assignNonClockedInvalidGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignFreshLocalProgram
    (memoryAccess := some exactAccess))

private def assignErrorGuard : Bool :=
  assignLocalEvalFailGuard && assignGlobalEvalFailGuard &&
    assignFreshLocalGuard && assignFreshGlobalGuard &&
    assignNonClockedEvalFailGuard && assignNonClockedInvalidGuard

#guard assignErrorGuard

def runChecks : IO Bool := do
  if assignLocalEvalFailGuard then
    IO.println "PASS exact-state Assign failing local source keeps state and clock"
  else
    IO.println "FAIL exact-state Assign failing local source"
  if assignGlobalEvalFailGuard then
    IO.println "PASS exact-state Assign failing global source keeps state and clock"
  else
    IO.println "FAIL exact-state Assign failing global source"
  if assignFreshLocalGuard then
    IO.println "PASS exact-state Assign invalid local destination keeps state and clock"
  else
    IO.println "FAIL exact-state Assign invalid local destination"
  if assignFreshGlobalGuard then
    IO.println "PASS exact-state Assign invalid global destination keeps state and clock"
  else
    IO.println "FAIL exact-state Assign invalid global destination"
  if assignNonClockedEvalFailGuard then
    IO.println "PASS non-clocked Assign failing source rejected with Error"
  else
    IO.println "FAIL non-clocked Assign failing source"
  if assignNonClockedInvalidGuard then
    IO.println "PASS non-clocked Assign invalid destination rejected with Error"
  else
    IO.println "FAIL non-clocked Assign invalid destination"
  pure assignErrorGuard

end Flapjack.Test.PanSemAssignErrorExactParity