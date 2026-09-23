import Flapjack.Pancake.Semantics.LoopSem

/-!
# Parity for the word-parametric `loopSem$evaluate` machine

The equation shapes are checked definitionally against `evaluate_def`
(`cakeml/pancake/semantics/loopSemScript.sml:278-360`) at a fully generic
word/FFI type, so the same machine serves the source probe (`W = Nat`,
`F = LoopWordLoc`) and the production `BitVec` IR.

The executable observations reuse the checked-in HOL-EVAL fixture
`scripts/hol-probes/loop_sem_evaluate_probe.out`, whose state is
`(8,'ffi) loopSem$state` (`W = BitVec 8`).  The rows that do not invoke an
effect hook are reproduced exactly: `skip`, `break`, `continue`, the tail call
whose callee returns `NONE`, and the clock-zero `tick` timeout.  The
`assign`/`seq_return` rows exercise the expression hook and are covered by the
production-hook regression (`flapjack-s6a.3`).
-/

namespace Flapjack.Test.LoopSemEvaluateParity

open Flapjack

/-! ## Equation shapes -/

example {W F : Type} (fuel : Nat) (hooks : LoopEvaluateHooks W F)
    (state : LoopMachineState W F) :
    evaluateLoop (fuel + 1) hooks .skip state = (none, state) := by
  simp [evaluateLoop]

example {W F : Type} (hooks : LoopEvaluateHooks W F)
    (program : LoopProg W) (state : LoopMachineState W F) :
    evaluateLoop 0 hooks program state = (some .error, state) := by
  simp [evaluateLoop]

example {W F : Type} (fuel : Nat) (hooks : LoopEvaluateHooks W F)
    (state : LoopMachineState W F) :
    evaluateLoop (fuel + 1) hooks .fail state = (some .error, state) := by
  simp [evaluateLoop]

example {W F : Type} (fuel label : Nat) (hooks : LoopEvaluateHooks W F)
    (state : LoopMachineState W F) :
    evaluateLoop (fuel + 1) hooks (.break label) state =
      (some (.break label), state) := by
  simp [evaluateLoop]

example {W F : Type} (fuel label : Nat) (hooks : LoopEvaluateHooks W F)
    (state : LoopMachineState W F) :
    evaluateLoop (fuel + 1) hooks (.continue label) state =
      (some (.continue label), state) := by
  simp [evaluateLoop]

example {W F : Type} (fuel : Nat) (hooks : LoopEvaluateHooks W F)
    (state : LoopMachineState W F) (name : Nat)
    (expression : LoopExp W) :
    evaluateLoop (fuel + 1) hooks (.assign name expression) state =
      (match hooks.eval state expression with
       | none => (some .error, state)
       | some value =>
           (none, { state with locals := loopSetVar state.locals name value })) := by
  cases h : hooks.eval state expression <;> simp [h, evaluateLoop]

/-! ## Executable HOL-EVAL observations -/

/-- The HOL probe state is `(8,'ffi) loopSem$state`, so the word payload is
    `BitVec 8`; the FFI event type is irrelevant to these rows. -/
def probeState (clock : Nat) : LoopMachineState (BitVec 8) LoopWordLoc :=
  { locals := fun _ => none
  , globals := fun _ => none
  , memory := fun _ => none
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := clock
  , code := []
  , be := false
  , ffi := .word 0
  , baseAddr := 0
  , topAddr := 0 }

/-- Dummy hooks for programs that provably never invoke an effect operation;
    the expression/primitive/memory hooks are exercised by `flapjack-s6a.3`. -/
def noEffectHooks : LoopEvaluateHooks (BitVec 8) LoopWordLoc where
  eval := fun _ _ => none
  primitive := fun _ _ => none
  arith := fun _ _ => none
  store := fun _ _ _ => none
  setGlobal := fun state _ _ => state
  load32 := fun _ _ => none
  loadByte := fun _ _ => none
  store32 := fun _ _ _ => none
  storeByte := fun _ _ _ => none
  compare := fun _ _ _ => false
  shMem := fun _ _ _ state => (some .error, state)
  ffi := fun _ _ _ _ _ _ state => (some .error, state)

def skipResult : LoopMachineStep (BitVec 8) LoopWordLoc :=
  evaluateLoop 5 noEffectHooks .skip (probeState 5)

def breakResult : LoopMachineStep (BitVec 8) LoopWordLoc :=
  evaluateLoop 5 noEffectHooks (.break 3) (probeState 5)

def continueResult : LoopMachineStep (BitVec 8) LoopWordLoc :=
  evaluateLoop 5 noEffectHooks (.continue 2) (probeState 5)

def tickState : LoopMachineState (BitVec 8) LoopWordLoc :=
  { probeState 0 with
    locals := fun name => if name = 1 then some (.word 7) else none }

def tickResult : LoopMachineStep (BitVec 8) LoopWordLoc :=
  evaluateLoop 5 noEffectHooks .tick tickState

def callState : LoopMachineState (BitVec 8) LoopWordLoc :=
  { probeState 5 with code := [(1, [], .skip)] }

def callResult : LoopMachineStep (BitVec 8) LoopWordLoc :=
  evaluateLoop 5 noEffectHooks (.call none (some 1) [] none) callState

def skipMatches : Bool :=
  skipResult.1.isNone && (skipResult.2.clock == 5)

def breakMatches : Bool :=
  breakResult.1 == some (.break 3)

def continueMatches : Bool :=
  continueResult.1 == some (.continue 2)

def tickMatches : Bool :=
  tickResult.1 == some .timeOut && (tickResult.2.locals 1).isNone
    && tickResult.2.clock == 0

def callMatches : Bool :=
  callResult.1 == some .error && (callResult.2.locals 1).isNone
    && callResult.2.clock == 4

#guard skipMatches
#guard breakMatches
#guard continueMatches
#guard tickMatches
#guard callMatches

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Loop evaluate skip", skipMatches),
    ("Loop evaluate break", breakMatches),
    ("Loop evaluate continue", continueMatches),
    ("Loop evaluate tick timeout", tickMatches),
    ("Loop evaluate tail call without result", callMatches)]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopSemEvaluateParity
