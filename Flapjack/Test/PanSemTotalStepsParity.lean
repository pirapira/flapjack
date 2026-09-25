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

/-- `Break` result check. -/
def isBreakResult (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | some .break => true
  | _ => false

/-- Partial total-evaluate dispatcher on a clock leaf: `Skip` completes normally. -/
def partialSkipGuard : Bool :=
  isNoneResult (panSemTotalEvaluatePartial (fun _ _ => none) stepsState .skip).1

/-- The dispatcher returns `Break` for `Break`. -/
def partialBreakGuard : Bool :=
  isBreakResult (panSemTotalEvaluatePartial (fun _ _ => none) stepsState .break).1

/-- The dispatcher handles `Assign` to a bound local, updating the binding. -/
def partialAssignGuard : Bool :=
  let result := panSemTotalEvaluatePartial (fun _ _ => none) stepsState
    (.assign .local "x" (.const (BitVec.ofNat 64 9)))
  isNoneResult result.1 && wordAt result.2.locals "x" 9

/-- The dispatcher recurses into the `Dec` body and restores the previous local. -/
def partialDecGuard : Bool :=
  let result := panSemTotalEvaluatePartial (fun _ _ => none) stepsState
    (.dec "x" Shape.one (.const (BitVec.ofNat 64 9)) (.return (.var .local "x")))
  isReturnedWord 9 result.1 && wordAt result.2.locals "x" 7

/-- A not-yet-assembled clause (`Seq`) returns `SOME Error` unchanged. -/
def partialSeqGuard : Bool :=
  isErrorResult (panSemTotalEvaluatePartial (fun _ _ => none) stepsState
    (.seq .skip .skip)).1

def partialEvaluateGuard : Bool :=
  partialSkipGuard && partialBreakGuard && partialAssignGuard &&
    partialDecGuard && partialSeqGuard

/-- Deterministic mapped-read/write oracle returning eight zero bytes. -/
def shMemTestFfi : FfiState Unit :=
  { oracle := fun _ _ _ bytes => .returned () bytes
    state := ()
    ioEvents := [] }

def shMemTestState : PanSemState Word64 (FfiState Unit) :=
  { stepsState with
    locals := fun name => if name == "x" then some (.word (BitVec.ofNat 64 7)) else none
    sharedMemaddrs := fun _ => true
    ffi := shMemTestFfi }

def shMemLoadGuard : Bool :=
  let result := panSemTotalShMemLoadClause shMemTestState .opW .local "x" (.const (BitVec.ofNat 64 0))
  isNoneResult result.1 && wordAt result.2.locals "x" 0

def shMemLoadMissingGuard : Bool :=
  isErrorResult (panSemTotalShMemLoadClause shMemTestState .opW .local "y"
    (.const (BitVec.ofNat 64 0))).1

def shMemLoadUnsharedGuard : Bool :=
  isErrorResult (panSemTotalShMemLoadClause
    { shMemTestState with sharedMemaddrs := fun _ => false }
    .opW .local "x" (.const (BitVec.ofNat 64 0))).1

def shMemStoreGuard : Bool :=
  let result := panSemTotalShMemStoreClause shMemTestState .opW
    (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 5))
  isNoneResult result.1 && result.2.clock == shMemTestState.clock

def shMemStoreNonWordGuard : Bool :=
  isErrorResult (panSemTotalShMemStoreClause shMemTestState .opW
    (.const (BitVec.ofNat 64 0)) (.rStruct ([] : List (Exp Word64)))).1

/-- `TimeOut` result check. -/
def isTimeOutResult (result : Option (PanSemHOLResult Word64)) : Bool :=
  match result with
  | some .timeOut => true
  | _ => false

/-- A body/loop continuation stub that ignores the incoming state. -/
def whileStub (result : Option (PanSemHOLResult Word64))
    (next : PanSemState Word64 (FfiState Unit)) :
    PanSemState Word64 (FfiState Unit) →
      Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  fun _ => (result, next)

/-- HOL `While` with a zero condition completes normally with the state unchanged. -/
def whileCondZeroGuard : Bool :=
  isNoneResult (panSemTotalWhileStep stepsState (some (.word (BitVec.ofNat 64 0)))
    (whileStub none stepsState) (whileStub none stepsState)).1

/-- A failed condition evaluation is `SOME Error`. -/
def whileCondErrorGuard : Bool :=
  isErrorResult (panSemTotalWhileStep stepsState none
    (whileStub none stepsState) (whileStub none stepsState)).1

/-- A non-word condition is `SOME Error`. -/
def whileCondNonWordGuard : Bool :=
  isErrorResult (panSemTotalWhileStep stepsState (some (.rStruct []))
    (whileStub none stepsState) (whileStub none stepsState)).1

/-- A nonzero condition at clock zero times out with cleared locals. -/
def whileTimeoutGuard : Bool :=
  let result := panSemTotalWhileStep { stepsState with clock := 0 }
    (some (.word (BitVec.ofNat 64 1)))
    (whileStub none stepsState) (whileStub none stepsState)
  isTimeOutResult result.1 && result.2.clock == 0 && (result.2.locals "x").isNone

/-- A `Break` from the body stops the loop normally with the clamped clock. -/
def whileBreakGuard : Bool :=
  let result := panSemTotalWhileStep stepsState (some (.word (BitVec.ofNat 64 1)))
    (whileStub (some .break) stepsState) (whileStub none stepsState)
  isNoneResult result.1 && result.2.clock == 4

/-- A `Continue` from the body recurses into the loop continuation. -/
def whileContinueGuard : Bool :=
  isTimeOutResult (panSemTotalWhileStep stepsState (some (.word (BitVec.ofNat 64 1)))
    (whileStub (some .continue) stepsState) (whileStub (some .timeOut) stepsState)).1

def whileGuard : Bool :=
  whileCondZeroGuard && whileCondErrorGuard && whileCondNonWordGuard &&
    whileTimeoutGuard && whileBreakGuard && whileContinueGuard

/-- Evaluator stub: whatever program is run, return `result` and the state. -/
def decCallEval (result : Option (PanSemHOLResult Word64)) :
    Prog Word64 → PanSemState Word64 (FfiState Unit) →
      Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  fun _ state => (result, state)

/-- Missing arguments produce an error without touching the state. -/
def decCallNoneArgsGuard : Bool :=
  isErrorResult (panSemTotalDecCallStep stepsState none
    (some (.skip, (fun _ => none), Shape.one)) "r" Shape.one .skip
    (decCallEval none)).1

/-- A missing callee lookup produces an error. -/
def decCallNoneLookupGuard : Bool :=
  isErrorResult (panSemTotalDecCallStep stepsState (some []) none
    "r" Shape.one .skip (decCallEval none)).1

/-- Clock zero times out and clears the locals. -/
def decCallTimeoutGuard : Bool :=
  let result := panSemTotalDecCallStep { stepsState with clock := 0 } (some [])
    (some (.skip, (fun _ => none), Shape.one)) "r" Shape.one .skip
    (decCallEval none)
  isTimeOutResult result.1 && (result.2.locals "x").isNone

/-- A successful return whose shape matches runs the continuation and restores
    the previous binding of the result name. -/
def decCallSuccessGuard : Bool :=
  let result := panSemTotalDecCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one)) "r" Shape.one .skip
    (decCallEval (some (.returned (.word (BitVec.ofNat 64 11)))))
  isReturnedWord 11 result.1 && (result.2.locals "r").isNone

/-- A returned value whose shape does not match the declared result shape errors. -/
def decCallShapeMismatchGuard : Bool :=
  isErrorResult (panSemTotalDecCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one)) "r" Shape.one .skip
    (decCallEval (some (.returned (.rStruct []))))).1

def decCallGuard : Bool :=
  decCallNoneArgsGuard && decCallNoneLookupGuard && decCallTimeoutGuard &&
    decCallSuccessGuard && decCallShapeMismatchGuard

/-- The `caltyp` carrier of HOL `Call`. -/
abbrev CallType :=
  Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word64))

/-- Caller state with an extra bound local `y` for the destination test. -/
def callDestState : PanSemState Word64 (FfiState Unit) :=
  { stepsState with locals := fun name =>
      if name == "y" then some (.word (BitVec.ofNat 64 0))
      else stepsState.locals name }

/-- Caller state with an `E` exception shape and a bound local `h`. -/
def callHandlerState : PanSemState Word64 (FfiState Unit) :=
  { stepsState with
    locals := fun name =>
      if name == "h" then some (.word (BitVec.ofNat 64 0))
      else stepsState.locals name
    exceptionShapes := fun eid => if eid == "E" then some Shape.one else none }

/-- Missing arguments produce an error. -/
def callNoneArgsGuard : Bool :=
  isErrorResult (panSemTotalCallStep stepsState none
    (some (.skip, (fun _ => none), Shape.one)) none (decCallEval none)).1

/-- A missing callee lookup produces an error. -/
def callNoneLookupGuard : Bool :=
  isErrorResult (panSemTotalCallStep stepsState (some []) none
    none (decCallEval none)).1

/-- Clock zero times out and clears the locals. -/
def callTimeoutGuard : Bool :=
  let result := panSemTotalCallStep { stepsState with clock := 0 } (some [])
    (some (.skip, (fun _ => none), Shape.one)) none (decCallEval none)
  isTimeOutResult result.1 && (result.2.locals "x").isNone

/-- A returned value with `caltyp` `NONE` propagates the return and clears locals. -/
def callReturnNoCaltypGuard : Bool :=
  let result := panSemTotalCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one)) none
    (decCallEval (some (.returned (.word (BitVec.ofNat 64 11)))))
  isReturnedWord 11 result.1 && (result.2.locals "x").isNone

/-- `caltyp` `SOME (NONE, _)` keeps the caller's locals. -/
def callReturnNoDestGuard : Bool :=
  let result := panSemTotalCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one)) (some (none, none) : CallType)
    (decCallEval (some (.returned (.word (BitVec.ofNat 64 11)))))
  isNoneResult result.1 && wordAt result.2.locals "x" 7

/-- `caltyp` `SOME (SOME (rk, rt), _)` binds the validated result. -/
def callReturnLocalDestGuard : Bool :=
  let result := panSemTotalCallStep callDestState (some [])
    (some (.skip, (fun _ => none), Shape.one))
    (some (some (.local, "y"), none) : CallType)
    (decCallEval (some (.returned (.word (BitVec.ofNat 64 11)))))
  isNoneResult result.1 && wordAt result.2.locals "y" 11

/-- A returned value whose shape does not match the callee's return shape errors. -/
def callReturnShapeMismatchGuard : Bool :=
  isErrorResult (panSemTotalCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one)) none
    (decCallEval (some (.returned (.rStruct []))))).1

/-- Evaluator stub that distinguishes the body (`.skip`) from a `.tick` handler. -/
def callEval (bodyResult handlerResult : Option (PanSemHOLResult Word64)) :
    Prog Word64 → PanSemState Word64 (FfiState Unit) →
      Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  fun program state =>
    match program with
    | .tick => (handlerResult, state)
    | _ => (bodyResult, state)

/-- A matching handler is evaluated on the bound exception. -/
def callExceptionHandlerGuard : Bool :=
  isReturnedWord 99 (panSemTotalCallStep callHandlerState (some [])
    (some (.skip, (fun _ => none), Shape.one))
    (some (none, some ("E", "h", .tick)) : CallType)
    (callEval (some (.exception "E" (.word (BitVec.ofNat 64 5))))
      (some (.returned (.word (BitVec.ofNat 64 99)))))).1

/-- An exception with no matching handler propagates with cleared locals. -/
def callExceptionPropagateGuard : Bool :=
  let result := panSemTotalCallStep stepsState (some [])
    (some (.skip, (fun _ => none), Shape.one))
    (some (none, some ("E", "h", .skip)) : CallType)
    (decCallEval (some (.exception "F" (.word (BitVec.ofNat 64 5)))))
  isExceptionOf "F" 5 result.1 && (result.2.locals "x").isNone

def callGuard : Bool :=
  callNoneArgsGuard && callNoneLookupGuard && callTimeoutGuard &&
    callReturnNoCaltypGuard && callReturnNoDestGuard && callReturnLocalDestGuard &&
    callReturnShapeMismatchGuard && callExceptionHandlerGuard &&
    callExceptionPropagateGuard

def stepsGuard : Bool :=
  assignLocalGuard && assignMissingGuard && returnGuard && returnSizeErrorGuard &&
    returnErrorGuard &&
    raiseGuard && raiseMissingGuard && raiseShapeErrorGuard && raiseErrorGuard &&
    exprStepErrorGuard && exprStepSomeGuard &&
    primitiveOkGuard && primitiveShapeMismatchGuard && primitivePrimNoneGuard &&
    primitiveArgErrorGuard && exprListStepGuard && annotGuard &&
    storeGuard && storeNonWordGuard && storeErrorGuard &&
    store32Guard && store32ErrorGuard && storeByteGuard && storeByteErrorGuard &&
    decOkGuard && decShapeErrorGuard && decErrorGuard &&
    partialEvaluateGuard &&
    shMemLoadGuard && shMemLoadMissingGuard && shMemLoadUnsharedGuard &&
    shMemStoreGuard && shMemStoreNonWordGuard && whileGuard && decCallGuard &&
    callGuard

#eval stepsGuard
#guard stepsGuard

def runChecks : IO Bool := do
  if stepsGuard then
    IO.println "PASS total PanSem statement-clause assembly steps (Assign/Return/Raise/Primitive/Annot/Store/Dec/ShMem/While/DecCall/Call)"
    pure true
  else
    IO.println "FAIL total PanSem statement-clause assembly steps (Assign/Return/Raise)"
    pure false

end Flapjack.Test.PanSemTotalStepsParity
