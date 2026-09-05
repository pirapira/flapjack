import Flapjack.RiscV.CorrectnessLoop

/-!
Concrete regression for zero-labelled break termination in the fully
composed Loop and Word repeat evaluators.
-/

namespace Flapjack

open RiscV

def repeatControlLoopState : LoopState (Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def repeatControlWordState : State 64 :=
  zeroState 64

def repeatControlBody : LoopProg (Word 64) :=
  .break 0

theorem repeatControl_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      repeatControlLoopState.locals repeatControlWordState := by
  intro name value hvalue
  simp [repeatControlLoopState] at hvalue

theorem repeatControl_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.normal repeatControlLoopState)
      (.normal repeatControlWordState) := by
  apply loopToWord_repeat_loop_control_simulation
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [])
    (wordFunctions := [])
    (loopState := repeatControlLoopState)
    (wordState := repeatControlWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (body := repeatControlBody)
    (fuel := 2)
    (loopResult := .normal repeatControlLoopState)
    (wordResult := .normal repeatControlWordState)
    (hbody := by
      intro bodyFuel bodyLoop bodyWord bodyResult bodyWordResult hlocals hloop hword
      cases bodyFuel with
      | zero =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ bodyFuel =>
          have hloop' :
              some (.broke bodyLoop 0) = some bodyResult := by
            simpa [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
              repeatControlBody] using hloop
          have hword' :
              some (.broke bodyWord 0) = some bodyWordResult := by
            simpa [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
              repeatControlBody] using hword
          cases hloop'
          cases hword'
          exact ⟨rfl, hlocals⟩)
    (hlocals := repeatControl_mapped_locals)
    (hloop := by
      simp [evalLoopRepeatWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
        repeatControlBody, repeatControlLoopState])
    (hword := by
      simp [RiscV.evalWordLoopRepeatWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, loopToWordProg,
        repeatControlBody, repeatControlWordState])

end Flapjack
