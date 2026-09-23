import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake `Dec` equation

The source oracle is `scripts/hol-probes/pan_sem_dec_e2e_probe.out`, generated
from `panSemScript.sml:558-565` (`Dec`). It pins three branches: an accepted
declaration runs its body, preserves the clock, and restores the declared local
to its previous binding; a shape mismatch is rejected (`SOME Error`); and a
declaration whose initialiser does not evaluate is rejected.

`panSemEvaluateCodeStateWithFuel_dec` is the untagged production equation. The
body call reuses the predecessor fuel, so it is stated over the explicit-fuel
evaluator; the reduced result representation means the statement is not HOL's
`(prog_result, state)` pair, so it carries no `@[hol]` tag.
-/

namespace Flapjack.Test.PanSemDecParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def decState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
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

def decEvaluate (clock fuel : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateCodeStateWithFuel statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (fuel + 1) (decState clock) program

def decBodyLocals : VarName → Option (PanValue Word64) :=
  updatePanValueMap (decState 5).locals "x" (.word (BitVec.ofNat 64 7))

def decRestoredLocals : VarName → Option (PanValue Word64) :=
  restorePanValueLocal (updatePanValueMap decBodyLocals "x" (.word (BitVec.ofNat 64 7)))
    "x" (some (.word (BitVec.ofNat 64 3)))

def decOkOutcome : PanValueFfiClockResult Word64 Unit :=
  (.control (.normal decRestoredLocals (decState 5).globals
      (decState 5).memory (decState 5).ffi), 5)

theorem dec_ok_eq :
    decEvaluate 5 3 (.dec "x" Shape.one (.const (BitVec.ofNat 64 7))
        (.assign .local "x" (.const (BitVec.ofNat 64 7)))) =
      some decOkOutcome := by
  unfold decEvaluate decOkOutcome
  rw [panSemEvaluateCodeStateWithFuel_dec]
  simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
    evalPanValueExpCounted,
    decState, evalPanValueExp, panValueAssignmentValid, panValueShape,
    panShapeMatches, updatePanValueMap, panValueFfiClockRestoreLocal,
    restorePanValueFfiLocal, decBodyLocals, decRestoredLocals]

theorem dec_shape_mismatch_eq :
    decEvaluate 5 3 (.dec "x" (Shape.named "Other") (.const (BitVec.ofNat 64 7))
        .skip) = none := by
  unfold decEvaluate
  rw [panSemEvaluateCodeStateWithFuel_dec]
  simp [decState, evalPanValueExp, panValueShape, panShapeMatches]

theorem dec_eval_missing_eq :
    decEvaluate 5 3 (.dec "x" Shape.one (.var .local "z") .skip) = none := by
  unfold decEvaluate
  rw [panSemEvaluateCodeStateWithFuel_dec]
  simp [decState, evalPanValueExp]

def isWord3 : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 3
  | _ => false

def decOkGuard : Bool :=
  match decEvaluate 5 3 (.dec "x" Shape.one (.const (BitVec.ofNat 64 7))
      (.assign .local "x" (.const (BitVec.ofNat 64 7)))) with
  | some (.control (.normal locals _ _ _), 5) => isWord3 (locals "x")
  | _ => false

def decShapeMismatchGuard : Bool :=
  (decEvaluate 5 3 (.dec "x" (Shape.named "Other") (.const (BitVec.ofNat 64 7))
      .skip)).isNone

def decEvalMissingGuard : Bool :=
  (decEvaluate 5 3 (.dec "x" Shape.one (.var .local "z") .skip)).isNone

def decGuard : Bool :=
  decOkGuard && decShapeMismatchGuard && decEvalMissingGuard

#guard decGuard

def runChecks : IO Bool := do
  if decOkGuard then
    IO.println "PASS panSem Dec accepted body restores declared local"
  else IO.println "FAIL panSem Dec accepted body restores declared local"
  if decShapeMismatchGuard then
    IO.println "PASS panSem Dec shape mismatch rejected"
  else IO.println "FAIL panSem Dec shape mismatch rejected"
  if decEvalMissingGuard then
    IO.println "PASS panSem Dec initialiser failure rejected"
  else IO.println "FAIL panSem Dec initialiser failure rejected"
  pure decGuard

end Flapjack.Test.PanSemDecParity
