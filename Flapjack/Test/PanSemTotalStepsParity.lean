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

/-- A `Return` of a value whose shape size is at most 32 returns it and clears
    the locals (HOL `empty_locals`). -/
def returnGuard : Bool :=
  let result := panSemTotalReturnClause stepsState (.const (BitVec.ofNat 64 3))
  isReturnedWord 3 result.1 && (result.2.locals "x").isNone

/-- A `Return` of a value whose shape size exceeds 32 is `SOME Error`. -/
def returnSizeErrorGuard : Bool :=
  isErrorResult (panSemTotalReturnClause stepsState
    (.rStruct (List.replicate 33 (.const (BitVec.ofNat 64 0))))).1

/-- A `Return` whose expression fails is `SOME Error`. -/
def returnErrorGuard : Bool :=
  isErrorResult (panSemTotalReturnClause stepsState (.var .local "missing")).1

/-- A state with declared exception shape `E` = `One`. -/
def raiseState : PanSemState Word64 (FfiState Unit) :=
  { stepsState with exceptionShapes := fun name =>
      if name == "E" then some Shape.one else none }

/-- A `Raise` of an `One`-shaped value under a matching declared exception
    returns `SOME (Exception eid v)` and clears the locals. -/
def raiseGuard : Bool :=
  let result := panSemTotalRaiseClause raiseState "E" (.const (BitVec.ofNat 64 4))
  isExceptionOf "E" 4 result.1 && (result.2.locals "x").isNone

/-- A `Raise` of an undeclared exception is `SOME Error`. -/
def raiseMissingGuard : Bool :=
  isErrorResult (panSemTotalRaiseClause raiseState "F" (.const (BitVec.ofNat 64 4))).1

/-- A `Raise` whose value shape does not match the declared exception is
    `SOME Error`. -/
def raiseShapeErrorGuard : Bool :=
  isErrorResult (panSemTotalRaiseClause raiseState "E" (.rStruct [])).1

/-- A `Raise` whose expression fails is `SOME Error`. -/
def raiseErrorGuard : Bool :=
  isErrorResult (panSemTotalRaiseClause raiseState "E" (.var .local "missing")).1

/-- The shared glue leaves a failed expression as `SOME Error`. -/
def exprStepErrorGuard : Bool :=
  isErrorResult (panSemTotalExprStep stepsState (.var .local "missing")
    (fun value => (some (.returned value), stepsState))).1

/-- The shared glue hands a produced value to its continuation. -/
def exprStepSomeGuard : Bool :=
  isReturnedWord 5 (panSemTotalExprStep stepsState (.const (BitVec.ofNat 64 5))
    (fun value => (some (.returned value), stepsState))).1

/-- A `Primitive` handler producing a valid word binding succeeds. -/
def primitiveOkGuard : Bool :=
  let result := panSemTotalPrimitiveClause stepsState "x" .addCarry
    [.const (BitVec.ofNat 64 1)] (fun _ _ => some (.word (BitVec.ofNat 64 9)))
  isNoneResult result.1 && wordAt result.2.locals "x" 9

/-- A `Primitive` handler producing a shape-incompatible value is `SOME Error`. -/
def primitiveShapeMismatchGuard : Bool :=
  let result := panSemTotalPrimitiveClause stepsState "x" .addCarry
    [.const (BitVec.ofNat 64 1)] (fun _ _ => some (.rStruct []))
  isErrorResult result.1 && wordAt result.2.locals "x" 7

/-- A `Primitive` handler returning `none` is `SOME Error`. -/
def primitivePrimNoneGuard : Bool :=
  isErrorResult (panSemTotalPrimitiveClause stepsState "x" .addCarry
    [.const (BitVec.ofNat 64 1)] (fun _ _ => none)).1

/-- A `Primitive` whose argument expression fails is `SOME Error`. -/
def primitiveArgErrorGuard : Bool :=
  isErrorResult (panSemTotalPrimitiveClause stepsState "x" .addCarry
    [.var .local "missing"] (fun _ _ => some (.word (BitVec.ofNat 64 9)))).1

/-- The list-expression glue leaves a failed argument list as `SOME Error`. -/
def exprListStepGuard : Bool :=
  isErrorResult (panSemTotalExprListStep stepsState
    [.const (BitVec.ofNat 64 1), .var .local "missing"]
    (fun _ => (none, stepsState))).1

/-- HOL `Annot` is erased: normal completion, state verbatim. -/
def annotGuard : Bool :=
  let result := panSemTotalAnnotClause stepsState "tag" "body"
  isNoneResult result.1 && wordAt result.2.locals "x" 7

/-- A store-enabled variant of `stepsState` (all addresses in the domain). -/
def storeState : PanSemState Word64 (FfiState Unit) :=
  { stepsState with memaddrs := fun _ => true }

/-- A store-enabled variant with a pre-existing word cell at address 0, needed by
    the byte/32-bit stores. -/
def store32State : PanSemState Word64 (FfiState Unit) :=
  { storeState with
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 0)) else none }

def memoryWordAt (memory : Word64 → Option (PanValue Word64)) (address expected : Nat) : Bool :=
  match memory (BitVec.ofNat 64 address) with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

/-- `Store` of a word value at a word address stores and completes normally. -/
def storeGuard : Bool :=
  let result := panSemTotalStoreClause storeState (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 42))
  isNoneResult result.1 && memoryWordAt result.2.memory 0 42

/-- `Store` with a non-word destination is `SOME Error`. -/
def storeNonWordGuard : Bool :=
  isErrorResult (panSemTotalStoreClause storeState (.rStruct [])
    (.const (BitVec.ofNat 64 42))).1

/-- `Store` whose destination expression fails is `SOME Error`. -/
def storeErrorGuard : Bool :=
  isErrorResult (panSemTotalStoreClause stepsState (.var .local "missing")
    (.const (BitVec.ofNat 64 42))).1

/-- `Store32` of a word value at an aligned address completes normally. -/
def store32Guard : Bool :=
  let result := panSemTotalStore32Clause store32State (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 0x11223344))
  isNoneResult result.1 && memoryWordAt result.2.memory 0 0x11223344

/-- `Store32` with no word cell at the address is `SOME Error`. -/
def store32ErrorGuard : Bool :=
  isErrorResult (panSemTotalStore32Clause storeState (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 3))).1

/-- `StoreByte` of a word value at an address with a word cell completes normally. -/
def storeByteGuard : Bool :=
  let result := panSemTotalStoreByteClause store32State (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 0xAB))
  isNoneResult result.1 && memoryWordAt result.2.memory 0 0xAB

/-- `StoreByte` with no word cell at the address is `SOME Error`. -/
def storeByteErrorGuard : Bool :=
  isErrorResult (panSemTotalStoreByteClause storeState (.const (BitVec.ofNat 64 0))
    (.const (BitVec.ofNat 64 0xAB))).1

/-- `Dec` body continuation: return the bound variable `x`. -/
def decBody (state : PanSemState Word64 (FfiState Unit)) :
    Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  match state.locals "x" with
  | some value => (some (.returned value), state)
  | none => (some .error, state)

/-- `Dec` of a valid local initialiser updates the binding, runs the body, then
    restores the previous local binding of the name. -/
def decOkGuard : Bool :=
  let result := panSemTotalDecClause stepsState "x" Shape.one
    (.const (BitVec.ofNat 64 9)) decBody
  isReturnedWord 9 result.1 && wordAt result.2.locals "x" 7

/-- `Dec` whose declared shape does not match the value shape is `SOME Error`. -/
def decShapeErrorGuard : Bool :=
  isErrorResult (panSemTotalDecClause stepsState "x" Shape.one
    (.rStruct []) decBody).1

/-- `Dec` whose initialiser fails to evaluate is `SOME Error`. -/
def decErrorGuard : Bool :=
  isErrorResult (panSemTotalDecClause stepsState "x" Shape.one
    (.var .local "missing") decBody).1

def stepsGuard : Bool :=
  assignLocalGuard && assignMissingGuard && returnGuard && returnSizeErrorGuard &&
    returnErrorGuard &&
    raiseGuard && raiseMissingGuard && raiseShapeErrorGuard && raiseErrorGuard &&
    exprStepErrorGuard && exprStepSomeGuard &&
    primitiveOkGuard && primitiveShapeMismatchGuard && primitivePrimNoneGuard &&
    primitiveArgErrorGuard && exprListStepGuard && annotGuard &&
    storeGuard && storeNonWordGuard && storeErrorGuard &&
    store32Guard && store32ErrorGuard && storeByteGuard && storeByteErrorGuard &&
    decOkGuard && decShapeErrorGuard && decErrorGuard

#eval stepsGuard
#guard stepsGuard

def runChecks : IO Bool := do
  if stepsGuard then
    IO.println "PASS total PanSem statement-clause assembly steps (Assign/Return/Raise/Primitive/Annot/Store/Dec)"
    pure true
  else
    IO.println "FAIL total PanSem statement-clause assembly steps (Assign/Return/Raise)"
    pure false

end Flapjack.Test.PanSemTotalStepsParity
