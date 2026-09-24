import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the total statement-clause assembly steps

Exercises `panSemTotalExprStep` and the `Assign`/`Return`/`Raise` total clause
helpers from `Flapjack/Pancake/Semantics/PanSem/TotalSteps.lean` on a concrete
RV64 source state:

* `Assign` to a bound local succeeds (HOL's normal completion, i.e. `NONE`) and
  updates the binding; `Assign` to an absent local is `SOME Error` with the state
  unchanged;
* `Return` of an evaluable expression is `SOME (Return v)` with the state
  unchanged; a failed expression is `SOME Error`;
* `Raise` mirrors `Return` with `SOME (Exception eid v)`.

These are untagged interface checks for the future exact `evaluate_def` port,
not a port of `evaluate` itself. The expression oracle is
`scripts/hol-probes/pan_sem_state_eval_probe.out`.
-/

namespace Flapjack.Test.PanSemTotalStepsParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def stepsState : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 7)) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def isNoneResult (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | none => true
  | _ => false

def isErrorResult (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def isReturnedWord (expected : Nat) (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | some (.returned (.word word)) => word == BitVec.ofNat 64 expected
  | _ => false

def isExceptionOf (exceptionId : ExceptionId) (expected : Nat)
    (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | some (.exception actual value) =>
      actual == exceptionId && (match value with
        | .word word => word == BitVec.ofNat 64 expected
        | _ => false)
  | _ => false

def wordAt (locals : VarName → Option (PanValue Word64)) (name : VarName)
    (expected : Nat) : Bool :=
  match locals name with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

/-- A bound local assignment succeeds and rewrites that local. -/
def assignLocalGuard : Bool :=
  let result := panSemTotalAssignClause stepsState .local "x" (.const (BitVec.ofNat 64 9))
  isNoneResult result.1 && wordAt result.2.locals "x" 9

/-- An assignment to an absent local is `SOME Error` with the state unchanged. -/
def assignMissingGuard : Bool :=
  let result := panSemTotalAssignClause stepsState .local "y" (.const (BitVec.ofNat 64 9))
  isErrorResult result.1 && wordAt result.2.locals "x" 7 && !(wordAt result.2.locals "y" 9)

/-- A `Return` of an evaluable expression returns the value, state unchanged. -/
def returnGuard : Bool :=
  let result := panSemTotalReturnClause stepsState (.const (BitVec.ofNat 64 3))
  isReturnedWord 3 result.1 && wordAt result.2.locals "x" 7

/-- A `Return` whose expression fails is `SOME Error`. -/
def returnErrorGuard : Bool :=
  isErrorResult (panSemTotalReturnClause stepsState (.var .local "missing")).1

/-- A `Raise` of an evaluable expression returns `SOME (Exception eid v)`. -/
def raiseGuard : Bool :=
  isExceptionOf "E" 4 (panSemTotalRaiseClause stepsState "E" (.const (BitVec.ofNat 64 4))).1

/-- The shared glue leaves a failed expression as `SOME Error`. -/
def exprStepErrorGuard : Bool :=
  isErrorResult (panSemTotalExprStep stepsState (.var .local "missing")
    (fun value => (some (.returned value), stepsState))).1

/-- The shared glue hands a produced value to its continuation. -/
def exprStepSomeGuard : Bool :=
  isReturnedWord 5 (panSemTotalExprStep stepsState (.const (BitVec.ofNat 64 5))
    (fun value => (some (.returned value), stepsState))).1

def stepsGuard : Bool :=
  assignLocalGuard && assignMissingGuard && returnGuard && returnErrorGuard &&
    raiseGuard && exprStepErrorGuard && exprStepSomeGuard

#eval stepsGuard
#guard stepsGuard

def runChecks : IO Bool := do
  if stepsGuard then
    IO.println "PASS total PanSem statement-clause assembly steps (Assign/Return/Raise)"
    pure true
  else
    IO.println "FAIL total PanSem statement-clause assembly steps (Assign/Return/Raise)"
    pure false

end Flapjack.Test.PanSemTotalStepsParity
