import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake semantic `If` result

The source oracle is `scripts/hol-probes/pan_sem_ite_e2e_probe.out`, generated
from `panSemScript.sml:617-620`. It pins four `If` outcomes against the
production evaluator:

* a nonzero word condition runs the then branch (clock unchanged);
* a zero word condition runs the else branch (clock unchanged);
* a non-word (unbound) condition is rejected with `SOME Error` and the
  unchanged state;
* a condition whose own evaluation fails (a load from an empty memory domain)
  is rejected with `SOME Error` and the unchanged state.
-/

namespace Flapjack.Test.PanSemIteParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def iteState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
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

def iteEvaluate (clock : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (iteState clock) program

def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

def isNormalAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.normal _ _ _ _), n), _) => n == clock
  | _ => false

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def thenAssign : Prog Word64 := .assign .local "x" (.const (BitVec.ofNat 64 9))

def trueIte : Prog Word64 := .ite (.const (BitVec.ofNat 64 1)) thenAssign .skip

def falseIte : Prog Word64 := .ite (.const (BitVec.ofNat 64 0)) thenAssign .skip

def nonwordIte : Prog Word64 := .ite (.var .local "z") thenAssign .skip

def failIte : Prog Word64 :=
  .ite (.load .one (.const (BitVec.ofNat 64 0))) thenAssign .skip

def iteTrueGuard : Bool :=
  isNormalAt 5 (iteEvaluate 5 trueIte) &&
    (match iteEvaluate 5 trueIte with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 9 (locals "x")
     | _ => false)

def iteFalseGuard : Bool :=
  isNormalAt 5 (iteEvaluate 5 falseIte) &&
    (match iteEvaluate 5 falseIte with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteNonwordGuard : Bool :=
  isErrorAt 5 (iteEvaluate 5 nonwordIte) &&
    (match iteEvaluate 5 nonwordIte with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteFailGuard : Bool :=
  isErrorAt 5 (iteEvaluate 5 failIte) &&
    (match iteEvaluate 5 failIte with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def iteGuard : Bool :=
  iteTrueGuard && iteFalseGuard && iteNonwordGuard && iteFailGuard

#guard iteGuard

def runChecks : IO Bool := do
  if iteTrueGuard then
    IO.println "PASS panSem If nonzero condition runs then branch"
  else IO.println "FAIL panSem If nonzero condition runs then branch"
  if iteFalseGuard then
    IO.println "PASS panSem If zero condition runs else branch"
  else IO.println "FAIL panSem If zero condition runs else branch"
  if iteNonwordGuard then
    IO.println "PASS panSem If non-word condition rejected with Error and unchanged state"
  else IO.println "FAIL panSem If non-word condition rejected with Error and unchanged state"
  if iteFailGuard then
    IO.println "PASS panSem If failing condition rejected with Error and unchanged state"
  else IO.println "FAIL panSem If failing condition rejected with Error and unchanged state"
  pure iteGuard

end Flapjack.Test.PanSemIteParity
