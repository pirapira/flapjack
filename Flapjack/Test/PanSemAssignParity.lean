import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `Assign` equation

The source oracle is `scripts/hol-probes/pan_sem_assign_e2e_probe.out`, generated
from `panSemScript.sml:566-572` (`Assign`). It pins three branches: an accepted
local assignment preserves the clock and writes the value; an assignment to a
fresh, unbound destination is rejected (`SOME Error`); and an assignment whose
source expression does not evaluate is rejected.

`panSemEvaluateCodeStateWithPostState_assign` is the untagged production
equation; the reduced result representation means the statement is not HOL's
`(prog_result, state)` pair, so it carries no `@[hol]` tag.
-/

namespace Flapjack.Test.PanSemAssignParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

abbrev AssignResult :=
  Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))

def assignState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun name =>
      if name == "g" then some (.word (BitVec.ofNat 64 4)) else none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def assignEvaluate (clock : Nat) (program : Prog Word64) : AssignResult :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (assignState clock) program

def assignLocalWrite : VarName → Option (PanValue Word64) :=
  updatePanValueMap (assignState 5).locals "x" (.word (BitVec.ofNat 64 7))

def assignLocalOkOutcome : PanValueFfiClockResult Word64 Unit :=
  (.control (.normal assignLocalWrite (assignState 5).globals
      (assignState 5).memory (assignState 5).ffi), 5)

def assignLocalOkPost : PanSemState Word64 (FfiState Unit) :=
  { assignState 5 with locals := assignLocalWrite }

def assignLocalOkExpected : AssignResult :=
  some (assignLocalOkOutcome, assignLocalOkPost)

theorem assign_local_ok_eq :
    assignEvaluate 5 (.assign .local "x" (.const (BitVec.ofNat 64 7))) =
      assignLocalOkExpected := by
  unfold assignEvaluate assignLocalOkExpected
  rw [panSemEvaluateCodeStateWithPostState_assign]
  simp [assignState, evalPanValueExp, panValueAssignmentValid, panValueShape,
    panShapeMatches, assignLocalOkOutcome, assignLocalOkPost, assignLocalWrite]

theorem assign_fresh_invalid_eq :
    assignEvaluate 5 (.assign .local "y" (.const (BitVec.ofNat 64 7))) = none := by
  unfold assignEvaluate
  rw [panSemEvaluateCodeStateWithPostState_assign]
  simp [assignState, evalPanValueExp, panValueAssignmentValid]

theorem assign_eval_missing_eq :
    assignEvaluate 5 (.assign .local "x" (.var .local "z")) = none := by
  unfold assignEvaluate
  rw [panSemEvaluateCodeStateWithPostState_assign]
  simp [assignState, evalPanValueExp]

def isWord7 : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 7
  | _ => false

def assignLocalOkGuard : Bool :=
  match assignEvaluate 5 (.assign .local "x" (.const (BitVec.ofNat 64 7))) with
  | some ((.control (.normal locals _ _ _), 5), post) =>
      isWord7 (locals "x") && isWord7 (post.locals "x") && post.clock = 5
  | _ => false

def assignFreshGuard : Bool :=
  (assignEvaluate 5 (.assign .local "y" (.const (BitVec.ofNat 64 7)))).isNone

def assignMissingGuard : Bool :=
  (assignEvaluate 5 (.assign .local "x" (.var .local "z"))).isNone

def assignGuard : Bool :=
  assignLocalOkGuard && assignFreshGuard && assignMissingGuard

#guard assignGuard

def runChecks : IO Bool := do
  if assignLocalOkGuard then
    IO.println "PASS panSem Assign accepted local write preserves clock and locals"
  else IO.println "FAIL panSem Assign accepted local write preserves clock and locals"
  if assignFreshGuard then
    IO.println "PASS panSem Assign fresh destination rejected"
  else IO.println "FAIL panSem Assign fresh destination rejected"
  if assignMissingGuard then
    IO.println "PASS panSem Assign source evaluation failure rejected"
  else IO.println "FAIL panSem Assign source evaluation failure rejected"
  pure assignGuard

end Flapjack.Test.PanSemAssignParity
