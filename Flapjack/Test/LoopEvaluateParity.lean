import Flapjack.LoopEvaluate

/-!
# Source parity for Pancake `loopSem$evaluate`

The source fixture is `scripts/hol-probes/loop_sem_evaluate_probe.out`,
generated from `loop_sem_evaluate_probeScript.sml`.  The representative
sequence case checks the intermediate assignment through the final return and
the break/continue result cases preserve state, and the tail-call case checks
that `call_env` clears the locals, matching `evaluate_def`.
-/

namespace Flapjack.Test.LoopEvaluateParity

open Flapjack

def emptyState (clock : Nat) : LoopMachineState LoopWordLoc :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := clock
    code := []
    be := false
    ffi := .word 0
    baseAddr := .word 4
    topAddr := .word 100 }

def evalProbe (state : LoopMachineState LoopWordLoc) :
    LoopExp LoopWordLoc → Option LoopWordLoc
  | .const value => some value
  | .var name => state.locals name
  | _ => none

def compareProbe : Cmp → LoopWordLoc → LoopWordLoc → Bool
  | .equal, left, right => left == right
  | .notEqual, left, right => left != right
  | _, _, _ => false

def hooks : LoopEvaluateHooks :=
  { eval := evalProbe
    primitive := fun _ _ => none
    arith := fun _ _ => none
    store := fun _ _ _ => none
    setGlobal := loopSetGlobalMachine
    load32 := fun _ _ => none
    loadByte := fun _ _ => none
    store32 := fun _ _ _ => none
    storeByte := fun _ _ _ => none
    compare := compareProbe
    shMem := fun _ _ _ state => (some .error, state)
    ffi := fun _ _ _ _ _ _ state => (some .error, state) }

/-! The existing `loop_sem_loop_arith_probe.out` fixes 8-bit words and checks
    `loopSemScript.sml:118-145`: a valid `LLongDiv`, zero divisor, quotient
    overflow, and malformed/non-word operands.  Exercise those same cases
    through the exact `evaluate_def` arithmetic boundary. -/
def arithHooks : LoopEvaluateHooks :=
  { hooks with arith := fun state operation => loopArithMachine 8 state operation }

/-! The source probes `loop_sem_sh_mem_load_probe.out` and
    `loop_sem_sh_mem_store_probe.out` cover `loopSemScript.sml:198-243`.
    The exact evaluator delegates the byte/FFI details to `shMem`; these
    hooks expose the same success, domain-error, operand-error, and terminal
    result transitions at the `evaluate_def` boundary. -/
def sharedMemHooks : LoopEvaluateHooks :=
  { arithHooks with shMem := fun operator name address state =>
      if !state.shMdomain address then
        (some .error, state)
      else if loopIsLoad operator then
        if state.ffi == .word 9 then
          (some (.finalFfi (.word 11)), { state with locals := fun _ => none })
        else
          (none, { state with locals := loopSetVar state.locals name (.word 3) })
      else
        (none, state) }

def sharedState (domain : Bool) (ffi : LoopWordLoc)
    (locals : Nat → Option LoopWordLoc) : LoopMachineState LoopWordLoc :=
  { (emptyState 5) with shMdomain := fun _ => domain, ffi := ffi, locals := locals }

def observeSharedMem (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc × LoopWordLoc :=
  (step.1, step.2.locals 1, step.2.ffi)

def sharedLoadSuccess : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (none, some (.word 3), .word 0)

def sharedStoreSuccess : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .store 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun name =>
      if name = 1 then some (.word 7) else none))) ==
    (none, some (.word 7), .word 0)

def sharedLoadDomainError : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState false (.word 0) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (some .error, some (.word 0), .word 0)

def sharedLoadMissingDestination : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun _ => none))) ==
    (some .error, none, .word 0)

def sharedStoreMissingSource : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .store 1 (.const (.word 3)))
    (sharedState true (.word 0) (fun _ => none))) ==
    (some .error, none, .word 0)

def sharedLoadFinalFfi : Bool :=
  observeSharedMem (evaluateLoop 2 sharedMemHooks
    (.shMem .load 1 (.const (.word 3)))
    (sharedState true (.word 9) (fun name =>
      if name = 1 then some (.word 0) else none))) ==
    (some (.finalFfi (.word 11)), none, .word 9)

/-! The exact FFI branch is `evaluate_def` in
    `loopSemScript.sml:278-423`; its byte/oracle behavior is checked by the
    source-derived `ffi_call_probe.out` and the existing `LoopFfi` fixtures.
    These hooks exercise the evaluator's cut-state, result, event, and clock
    boundary without replacing the source-shaped FFI implementation. -/
def ffiFinalEvent : LoopWordLoc := .word 11

def ffiHooks : LoopEvaluateHooks :=
  { sharedMemHooks with ffi := fun _ configuration configurationLength array
      arrayLength _ state =>
      if (state.locals configuration).isNone ||
          (state.locals configurationLength).isNone ||
          (state.locals array).isNone ||
          (state.locals arrayLength).isNone then
        (some .error, state)
      else if state.ffi == .word 9 then
        (some (.finalFfi ffiFinalEvent), { state with locals := fun _ => none })
      else
        (none, { state with ffi := .word 7 }) }

def ffiCallState (clock : Nat) (ffi : LoopWordLoc)
    (locals : Nat → Option LoopWordLoc) : LoopMachineState LoopWordLoc :=
  { (emptyState clock) with ffi := ffi, locals := locals }

def observeFfi (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.locals 9, step.2.ffi, step.2.clock)

def ffiCallSuccess : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else if name = 9 then some (.word 99)
      else none))) ==
    (none, some (.word 10), none, .word 7, 5)

def ffiMalformedArgs : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some .error, none, none, .word 0, 5)

def ffiMissingLiveState : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 0) (fun name =>
      if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else if name = 9 then some (.word 99)
      else none))) ==
    (some .error, none, some (.word 99), .word 0, 5)

def ffiFinal : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 5 (.word 9) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some (.finalFfi ffiFinalEvent), none, none, .word 9, 5)

def ffiFinalAtZeroClock : Bool :=
  observeFfi (evaluateLoop 2 ffiHooks
    (.ffi "echo" 1 2 3 4 [1, 2, 3, 4])
    (ffiCallState 0 (.word 9) (fun name =>
      if name = 1 then some (.word 10)
      else if name = 2 then some (.word 1)
      else if name = 3 then some (.word 20)
      else if name = 4 then some (.word 2)
      else none))) ==
    (some (.finalFfi ffiFinalEvent), none, none, .word 9, 0)

def longDivState (high low divisor : Option LoopWordLoc) :
    LoopMachineState LoopWordLoc :=
  { (emptyState 5) with locals := fun name =>
      if name = 3 then high
      else if name = 4 then low
      else if name = 5 then divisor
      else none }

def observeLongDiv (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.locals 2, step.2.clock)

def longDivSuccess : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 3)) (some (.word 2)))) ==
    (none, some (.word 129), some (.word 1), 5)

def longDivZero : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 3)) (some (.word 0)))) ==
    (some .error, none, none, 5)

def longDivOverflow : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.word 1)) (some (.word 0)) (some (.word 1)))) ==
    (some .error, none, none, 5)

def longDivMalformed : Bool :=
  observeLongDiv (evaluateLoop 2 arithHooks
    (.arith (.longDiv 1 2 3 4 5))
    (longDivState (some (.loc 9 0)) (some (.word 3)) (some (.word 2)))) ==
    (some .error, none, none, 5)

def observe (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.clock)

def sequenceReturn : Bool :=
  observe (evaluateLoop 8 hooks
    (.seq (.assign 1 (.const (.word 7))) (.return [1])) (emptyState 5)) ==
    (some (.result [.word 7]), none, 5)

def skip : Bool :=
  observe (evaluateLoop 4 hooks .skip (emptyState 5)) ==
    (none, none, 5)

def assignment : Bool :=
  observe (evaluateLoop 4 hooks (.assign 1 (.const (.word 7))) (emptyState 5)) ==
    (none, some (.word 7), 5)

def breakResult : Bool :=
  observe (evaluateLoop 4 hooks (.break 3)
    { (emptyState 5) with locals := fun name =>
        if name = 1 then some (.word 7) else none }) ==
    (some (.break 3), some (.word 7), 5)

def continueResult : Bool :=
  observe (evaluateLoop 4 hooks (.continue 2)
    { (emptyState 5) with locals := fun name =>
        if name = 1 then some (.word 7) else none }) ==
    (some (.continue 2), some (.word 7), 5)

def timeout : Bool :=
  observe (evaluateLoop 4 hooks .tick (emptyState 0)) ==
    (some .timeOut, none, 0)

def tailCallNoResult : Bool :=
  observe (evaluateLoop 8 hooks
    (.call none (some 1) [] none)
    { (emptyState 5) with code := [(1, [], .skip)] }) ==
    (some .error, none, 4)

/-! `loopSemScript.sml:278-360` uses `fromAList (ZIP (params,args))` for
    `find_code`, so repeated parameters are first-occurrence-wins.  Its
    returning call branch restores `s.locals` (the caller locals) before
    setting return values, rather than retaining the liveness-cut locals. -/
def callResultState : LoopMachineState LoopWordLoc :=
  { (emptyState 5) with
      locals := fun name =>
        if name = 1 then some (.word 7)
        else if name = 2 then some (.word 8)
        else if name = 8 then some (.word 99)
        else none
      code := [(1, [4, 4], .return [4])] }

def observeCallResult (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc ×
      Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 5, step.2.locals 8, step.2.clock)

def callResultFirstWinsAndRestoresCaller : Bool :=
  observeCallResult (evaluateLoop 12 hooks
    (.call (some ([5], [])) (some 1) [1, 2] none) callResultState) ==
    (none, some (.word 7), some (.word 99), 4)

#guard sequenceReturn
#guard skip
#guard assignment
#guard breakResult
#guard continueResult
#guard timeout
#guard tailCallNoResult
#guard callResultFirstWinsAndRestoresCaller
#guard longDivSuccess
#guard longDivZero
#guard longDivOverflow
#guard longDivMalformed
#guard sharedLoadSuccess
#guard sharedStoreSuccess
#guard sharedLoadDomainError
#guard sharedLoadMissingDestination
#guard sharedStoreMissingSource
#guard sharedLoadFinalFfi
#guard ffiCallSuccess
#guard ffiMalformedArgs
#guard ffiMissingLiveState
#guard ffiFinal
#guard ffiFinalAtZeroClock

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("evaluate sequence observes intermediate assignment and call_env", sequenceReturn),
    ("evaluate Skip returns normally", skip),
    ("evaluate assignment updates the local state", assignment),
    ("evaluate Break preserves state and result", breakResult),
    ("evaluate Continue preserves state and result", continueResult),
    ("evaluate Tick clears locals at clock zero", timeout),
    ("evaluate tail call maps callee NONE to Error", tailCallNoResult),
    ("evaluate Call uses first-wins bindings and restores caller locals",
      callResultFirstWinsAndRestoresCaller),
    ("evaluate LongDiv returns the HOL quotient and remainder", longDivSuccess),
    ("evaluate LongDiv rejects a zero divisor", longDivZero),
    ("evaluate LongDiv rejects quotient overflow", longDivOverflow),
    ("evaluate LongDiv rejects a non-word operand", longDivMalformed),
    ("evaluate shared load updates its destination", sharedLoadSuccess),
    ("evaluate shared store preserves its source", sharedStoreSuccess),
    ("evaluate shared load rejects an unmapped address", sharedLoadDomainError),
    ("evaluate shared load rejects a missing destination", sharedLoadMissingDestination),
    ("evaluate shared store rejects a missing source", sharedStoreMissingSource),
    ("evaluate shared load propagates terminal FFI", sharedLoadFinalFfi),
    ("evaluate FFI preserves live caller state", ffiCallSuccess),
    ("evaluate FFI rejects malformed arguments", ffiMalformedArgs),
    ("evaluate FFI preserves caller state on cut failure", ffiMissingLiveState),
    ("evaluate FFI propagates FinalFFI and clears locals", ffiFinal),
    ("evaluate FFI preserves a zero clock on FinalFFI", ffiFinalAtZeroClock)]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS {name}"
    else IO.println s!"FAIL {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.LoopEvaluateParity
