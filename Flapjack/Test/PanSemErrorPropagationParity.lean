import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for nested propagation of the Pancake semantic `Error` result

The source oracle is `scripts/hol-probes/pan_sem_error_prop_e2e_probe.out`,
generated from `panSemScript.sml` (`Seq`, `While`). It nests a rejected `Dec`
inside `Seq` and `While` and pins that the explicit `SOME Error` result
propagates: `Seq` returns it with the clock unchanged, `While` returns it after
one iteration's clock reduction, and the rejected destination binding is
preserved in both cases.

The executable `Call` case is checked here too: a function whose body is the
same rejected declaration propagates the callee's explicit `Error` to the
caller. The full `panSem` state relation and a direct HOL `Call` oracle remain
out of scope for this regression.
-/

namespace Flapjack.Test.PanSemErrorPropagationParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def errorState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
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

def decMismatch : Prog Word64 :=
  .dec "x" (Shape.named "Other") (.const (BitVec.ofNat 64 7)) .skip

def errorEvaluate (clock : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (errorState clock) program

/-- True when evaluation yields exactly an explicit `Error` control result at
    the given clock. -/
def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

/-- The rejected declaration leaves the pre-existing local binding intact. -/
def isWord3 (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 3
  | _ => false

def localsPreserved (clock : Nat) (program : Prog Word64) : Bool :=
  match errorEvaluate clock program with
  | some ((.control (.error locals _ _ _), _), _) => isWord3 (locals "x")
  | _ => false

def seqProgram : Prog Word64 := .seq decMismatch .skip

def whileProgram : Prog Word64 := .while (.const (BitVec.ofNat 64 1)) decMismatch

def seqErrorGuard : Bool :=
  isErrorAt 5 (errorEvaluate 5 seqProgram) && localsPreserved 5 seqProgram

def whileErrorGuard : Bool :=
  isErrorAt 4 (errorEvaluate 5 whileProgram) && localsPreserved 5 whileProgram

def callCode : PanSemCodeMap Word64 := [("f", ([], decMismatch, Shape.one))]

def callState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { errorState clock with code := callCode }

def callEvaluate (clock : Nat) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (callState clock) (.call none "f" [])

def callErrorGuard : Bool :=
  isErrorAt 4 (callEvaluate 5)

def errorPropagationGuard : Bool :=
  seqErrorGuard && whileErrorGuard && callErrorGuard

#guard errorPropagationGuard

def runChecks : IO Bool := do
  if seqErrorGuard then
    IO.println "PASS panSem Seq propagates nested Error with unchanged state"
  else IO.println "FAIL panSem Seq propagates nested Error with unchanged state"
  if whileErrorGuard then
    IO.println "PASS panSem While propagates nested Error after one iteration"
  else IO.println "FAIL panSem While propagates nested Error after one iteration"
  if callErrorGuard then
    IO.println "PASS panSem Call propagates callee Error to caller"
  else IO.println "FAIL panSem Call propagates callee Error to caller"
  pure errorPropagationGuard

end Flapjack.Test.PanSemErrorPropagationParity