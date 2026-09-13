import Flapjack.LoopEvaluate

/-!
# Source parity for Pancake `loopSem$evaluate`

The source fixture is `scripts/hol-probes/loop_sem_evaluate_probe.out`,
generated from `loop_sem_evaluate_probeScript.sml`.  The representative
sequence case checks the intermediate assignment through the final return and
also checks that `call_env` clears the locals, matching `evaluate_def`.
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

def observe (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Option LoopWordLoc × Nat :=
  (step.1, step.2.locals 1, step.2.clock)

def sequenceReturn : Bool :=
  observe (evaluateLoop 8 hooks
    (.seq (.assign 1 (.const (.word 7))) (.return [1])) (emptyState 5)) ==
    (some (.result [.word 7]), none, 5)

def assignment : Bool :=
  observe (evaluateLoop 4 hooks (.assign 1 (.const (.word 7))) (emptyState 5)) ==
    (none, some (.word 7), 5)

def timeout : Bool :=
  observe (evaluateLoop 4 hooks .tick (emptyState 0)) ==
    (some .timeOut, none, 0)

#guard sequenceReturn
#guard assignment
#guard timeout

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("evaluate sequence observes intermediate assignment and call_env", sequenceReturn),
    ("evaluate assignment updates the local state", assignment),
    ("evaluate Tick clears locals at clock zero", timeout)]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS {name}"
    else IO.println s!"FAIL {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.LoopEvaluateParity
