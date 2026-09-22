import Flapjack.LoopCallCorrectness

namespace Flapjack.Test.LoopCallCorrectness

open Flapjack
open Flapjack.LoopCall

def locValueState : LoopState Nat :=
  { locals := fun name => if name = 2 then some 7 else none
    globals := fun _ => none
    memory := fun _ => none }

theorem locValue_compile_correct_fixture :
    evalLoopProg 1 locValueState
        (comp [(1, 2)] (.locValue 3 2) : LoopProg Nat × LocationEnv).1 =
        some (.normal { locValueState with
          locals := updateLoopLocal locValueState.locals 3 7 }) ∧
      labelsIn (comp [(1, 2)] (.locValue 3 2) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal locValueState.locals 3 7) := by
  apply comp_locValue_correct
  · simp [locValueState]
  · intro name source hlookup
    have hsource : source = 2 := by
      have hpair : 1 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      exact hpair.2.symm
    subst source
    exact ⟨7, by simp [locValueState]⟩

#check comp_locValue_correct

end Flapjack.Test.LoopCallCorrectness
