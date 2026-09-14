import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.fix_clock`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:150-152`.

The source keeps the result unchanged and clamps the returned state's clock to
the smaller of the old and new clocks.  The runtime state update is otherwise
record-preserving.
-/

namespace Flapjack

def crepFixClock (oldState : CrepRuntimeState α σ)
    (step : CrepRuntimeStep α σ ε) : CrepRuntimeStep α σ ε :=
  fixCrepRuntimeClock oldState step

@[simp] theorem crepFixClock_result (oldState : CrepRuntimeState α σ)
    (result : CrepRuntimeResult α ε) (newState : CrepRuntimeState α σ) :
    (crepFixClock oldState (result, newState)).1 = result := by
  rfl

@[simp] theorem crepFixClock_clock (oldState : CrepRuntimeState α σ)
    (result : CrepRuntimeResult α ε) (newState : CrepRuntimeState α σ) :
    (crepFixClock oldState (result, newState)).2.clock =
      min oldState.clock newState.clock := by
  rfl

@[simp] theorem crepFixClock_locals (oldState : CrepRuntimeState α σ)
    (result : CrepRuntimeResult α ε) (newState : CrepRuntimeState α σ) :
    (crepFixClock oldState (result, newState)).2.locals = newState.locals := by
  rfl

end Flapjack
