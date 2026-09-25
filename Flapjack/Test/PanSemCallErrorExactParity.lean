import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
Direct regression for the exact source `PanSemExactState` `Call` error
equations.  HOL evaluates the argument list with `OPT_MMAP (eval s) argexps`
before the callee lookup, so a memory-reading argument is gated by the source
`memaddrs`: an address outside the domain rejects the call with `SOME Error`
over the unchanged state, even when the raw memory function holds a cell.  An
unknown callee is likewise rejected.  The expected values are the original-HOL
`EVAL` rows in `scripts/hol-probes/pan_sem_call_error_state_probe.out`.
The return-shape conflict case is paired with
`pan_sem_call_return_shape_probe.out`: HOL accepts `goodret` because its
`state.code` entry declares `One`, regardless of any compatibility contracts
Lean might supply separately; the mismatched source code-map row returns
`Error`.

* `call_error_load_result=SOME Error`, `call_error_load_clock=5`,
  `call_error_load_locals=SOME (ValWord 3w)`;
* `call_error_domain_result=SOME Error`,
  `call_error_domain_locals=SOME (ValWord 3w)`;
* `call_error_missing_result=SOME Error`, `call_error_missing_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemCallErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false

/-- Access whose `memaddrs`-style domain is empty, so every read misses. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false)
    (fun _ => false) false

private def exactLegacy (clock : Nat) (locals : VarName → Option (PanValue Word64))
    (memory : Word64 → Option (PanValue Word64))
    (contracts : Option PanValueCallContracts) :
    PanSemEvaluateState Word64 Unit :=
  { structs := []
    functions := []
    locals := locals
    globals := fun _ => none
    memory := memory
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := 0
    topAddress := 100
    bytesInWord := 8
    memoryAccess := none
    contracts := contracts
    memoryHandler := none }

private def exactStateOfWith (access : PanValueMemoryAccess Word64)
    (legacy : PanSemEvaluateState Word64 Unit) : PanSemExactState Word64 Unit :=
  { legacy := legacy, memoryAccess := access }

private def exactStateOf (legacy : PanSemEvaluateState Word64 Unit) :
    PanSemExactState Word64 Unit :=
  exactStateOfWith exactAccess legacy

private def localsWithX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State with a present memory cell at address `8` and local `x`. -/
private def memoryState : PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 localsWithX exactMemory none

/-- State whose `memaddrs` domain is empty while the raw memory holds a cell. -/
private def emptyDomainState : PanSemExactState Word64 Unit :=
  exactStateOfWith emptyAccess <| exactLegacy 5 localsWithX exactMemory none

/-- State whose source evaluation fails immediately (no locals, no memory). -/
private def emptyState : PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 (fun _ => none) (fun _ => none) none

/-- State whose `Const` evaluation succeeds. -/
private def wordState : PanSemExactState Word64 Unit :=
  exactStateOf <| exactLegacy 5 (fun _ => some (.word 7)) (fun _ => none) none

private def evaluate (state : PanSemExactState Word64 Unit) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateExactState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def isWordValue (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ => n == clock && isWordValue localValue (locals "x")
      | _ => false
  | _ => false

private def loadHit : Exp Word64 := .load Shape.one (.const 8)

private def loadMiss : Exp Word64 := .load Shape.one (.const 11)

private def missingCall : Prog Word64 := .call none "f" [.const 1]

/-- Callee contracts declaring one `One`-shaped parameter for `f`. -/
private def parameterContracts : Option PanValueCallContracts :=
  some { returnShapes := [], exceptionShapes := [],
         parameterShapes := [("f", [("p", Shape.one)])] }

/-- State with a one-parameter callee `f` and matching contracts. -/
private def parameterState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 7)) (fun _ => none)
      parameterContracts) with functions := [("f", ["p"], .skip)] }

/-- Result matcher for the callee-fallthrough rejection: an `Error` at the
    decremented callee clock whose `p` local still holds the bound argument. -/
private def isFallThroughError (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (match locals "p" with
            | some (.word w) => w == BitVec.ofNat 64 value
            | _ => false)
      | _ => false
  | _ => false

/-- State whose callee `f` has body `Skip` and therefore falls through. -/
private def fallThroughState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 3)) (fun _ => none)
      parameterContracts) with functions := [("f", ["p"], .skip)] }

private def callFallThroughGuard : Bool :=
  isFallThroughError 4 1 (evaluate fallThroughState (.call none "f" [.const 1]))

/-- Result matcher for a callee that finishes with `Break` or `Continue`: an
    `Error` at the decremented callee clock whose `p` local holds the bound
    argument. -/
private def isTerminalError (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (match locals "p" with
            | some (.word w) => w == BitVec.ofNat 64 value
            | _ => false)
      | _ => false
  | _ => false

private def breakState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 3)) (fun _ => none)
      parameterContracts) with functions := [("f", ["p"], .break)] }

private def continueState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 3)) (fun _ => none)
      parameterContracts) with functions := [("f", ["p"], .continue)] }

private def callBreakGuard : Bool :=
  isTerminalError 4 1 (evaluate breakState (.call none "f" [.const 1]))

private def callContinueGuard : Bool :=
  isTerminalError 4 1 (evaluate continueState (.call none "f" [.const 1]))

/-- Result matcher for a callee that finishes with `Error`: the call propagates
    `SOME Error` through the catch-all `empty_locals st`, so the caller-visible
    locals are cleared at the decremented callee clock. -/
private def isPropagatedError (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (locals "p").isNone && (locals "x").isNone
      | _ => false
  | _ => false

/-- State whose callee `f` errors while evaluating its body: it reads address
    `11` outside the domain, so the callee finishes with `Error`. -/
private def calleeErrorState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 3)) (fun _ => none)
      parameterContracts) with
    functions := [("f", ["p"], .assign .local "p" (.load Shape.one (.const 11)))] }

private def callCalleeErrorGuard : Bool :=
  isPropagatedError 4 (evaluate calleeErrorState (.call none "f" [.const 1]))

/-- A compatibility contract deliberately disagrees with the source-shaped
    code map. The functions-list carrier has no source `returnShape`, so its
    optional contract table must not be used as HOL's code-map return shape. -/
private def returnInvalidContracts : Option PanValueCallContracts :=
  some { returnShapes := [("f", Shape.named "Other")], exceptionShapes := [], parameterShapes := [("f", [("p", Shape.one)])] }

private def returnInvalidState : PanSemExactState Word64 Unit :=
  exactStateOf <| { (exactLegacy 5 (fun _ => some (.word 3)) (fun _ => none) returnInvalidContracts) with functions := [("f", ["p"], .return (.const 0))] }

private def callReturnContractConflictGuard : Bool :=
  match evaluate returnInvalidState (.call none "f" [.const 1]) with
  | some (.control (.returned _ _ _ _ [.word value]), clock) =>
      clock == 4 && value == BitVec.ofNat 64 0
  | _ => false

private def callLoadMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState (.call none "f" [loadMiss]))

private def callParamArityGuard : Bool :=
  isErrorKeeping 5 7 (evaluate parameterState (.call none "f" []))

private def callParamShapeGuard : Bool :=
  isErrorKeeping 5 7 (evaluate parameterState (.call none "f" [.rStruct []]))

private def callMissingGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState missingCall)

private def callDomainGuard : Bool :=
  isErrorKeeping 5 3 (evaluate emptyDomainState (.call none "f" [loadHit]))

private def callGuard : Bool :=
  callLoadMissGuard && callMissingGuard && callDomainGuard &&
    callParamArityGuard && callParamShapeGuard && callFallThroughGuard &&
    callBreakGuard && callContinueGuard && callCalleeErrorGuard && callReturnContractConflictGuard

#guard callGuard

/-- A `Call` whose argument fails to evaluate returns `SOME Error` over the
    full exact state. -/
theorem callArgsMiss_eq :
    evaluate emptyState (.call none "f" [.var .local "z"]) =
      some (.control (.error emptyState.legacy.locals emptyState.legacy.globals
        emptyState.legacy.memory emptyState.legacy.ffi), emptyState.legacy.clock) := by
  apply panSemEvaluateExactState_call_error_of_arguments_none
  simp [emptyState, exactStateOf, exactStateOfWith, exactLegacy, evalPanValueExps,
    evalPanValueExp.evalPanValueExps, evalPanValueExp]

/-- A `Call` naming an unknown callee returns `SOME Error` over the full exact
    state. -/
theorem callMissing_eq :
    evaluate wordState missingCall =
      some (.control (.error wordState.legacy.locals wordState.legacy.globals
        wordState.legacy.memory wordState.legacy.ffi), wordState.legacy.clock) := by
  apply panSemEvaluateExactState_call_error_of_target_none (values := [.word 1])
  · simp [wordState, exactStateOf, exactStateOfWith, exactLegacy, evalPanValueExps,
      evalPanValueExp.evalPanValueExps, evalPanValueExp]
  · simp [wordState, exactStateOf, exactStateOfWith, exactLegacy, panValueCallTarget,
      lookupPanFunction]

/-- A `Call` whose argument list does not match the callee's parameter shapes
    returns `SOME Error` over the full exact state. -/
theorem callParamArity_eq :
    evaluate parameterState (.call none "f" []) =
      some (.control (.error parameterState.legacy.locals parameterState.legacy.globals
        parameterState.legacy.memory parameterState.legacy.ffi),
        parameterState.legacy.clock) := by
  apply panSemEvaluateExactState_call_error_of_parameters_invalid
    (parameters := ["p"]) (body := .skip) (values := [])
  · simp [parameterState, exactStateOf, exactStateOfWith, exactLegacy,
      evalPanValueExps, evalPanValueExp.evalPanValueExps]
  · simp [parameterState, exactStateOf, exactStateOfWith, exactLegacy,
      lookupPanFunction]
  · simp [parameterState, exactStateOf, exactStateOfWith, exactLegacy,
      parameterContracts, panValueParametersValid, lookupInfo,
      panValueValuesMatchShapes]

def runChecks : IO Bool := do
  if callLoadMissGuard then
    IO.println "PASS exact-state Call failing argument keeps state and clock"
  else IO.println "FAIL exact-state Call failing argument keeps state and clock"
  if callMissingGuard then
    IO.println "PASS exact-state Call unknown callee keeps state and clock"
  else IO.println "FAIL exact-state Call unknown callee keeps state and clock"
  if callDomainGuard then
    IO.println "PASS exact-state Call memory domain gates an argument read"
  else IO.println "FAIL exact-state Call memory domain gates an argument read"
  if callParamArityGuard then
    IO.println "PASS exact-state Call parameter arity mismatch keeps state and clock"
  else IO.println "FAIL exact-state Call parameter arity mismatch keeps state and clock"
  if callParamShapeGuard then
    IO.println "PASS exact-state Call parameter shape mismatch keeps state and clock"
  else IO.println "FAIL exact-state Call parameter shape mismatch keeps state and clock"
  if callFallThroughGuard then
    IO.println "PASS exact-state Call callee fallthrough rejects with Error and callee locals"
  else IO.println "FAIL exact-state Call callee fallthrough rejects with Error and callee locals"
  if callBreakGuard then
    IO.println "PASS exact-state Call callee break rejects with Error and callee locals"
  else IO.println "FAIL exact-state Call callee break rejects with Error and callee locals"
  if callContinueGuard then
    IO.println "PASS exact-state Call callee continue rejects with Error and callee locals"
  else IO.println "FAIL exact-state Call callee continue rejects with Error and callee locals"
  if callCalleeErrorGuard then
    IO.println "PASS exact-state Call callee error propagates cleared locals"
  else IO.println "FAIL exact-state Call callee error propagates cleared locals"
  if callReturnContractConflictGuard then
    IO.println "PASS functions-list Call ignores a conflicting compatibility return contract"
  else IO.println "FAIL functions-list Call ignores a conflicting compatibility return contract"
  pure callGuard

end Flapjack.Test.PanSemCallErrorExactParity
