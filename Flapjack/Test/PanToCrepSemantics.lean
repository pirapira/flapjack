import Flapjack.PanToCrepSemantics

namespace Flapjack.Test.PanToCrepSemantics

open Flapjack

def emptyPanHooks : PanSemanticsHooks Unit Unit where
  evaluate := fun _ => none
  ffiOutcome := fun _ => .failed

def emptyCrepState : CrepState Unit where
  locals := fun _ => none
  memory := fun _ => none
  globals := fun _ => none

def emptyCrepHooks : CrepSemanticsHooks Unit where
  evaluate := fun _ => (none, emptyCrepState)
  ioEvents := fun _ => []

theorem emptySemanticAgreement :
    PanCrepSemanticAgreement emptyPanHooks emptyCrepHooks := by
  constructor
  · intro clock
    rfl
  · intro clock
    simp [emptyPanHooks, emptyCrepHooks, crepForbiddenResult,
      panForbiddenResult]
  · intro clock
    simp [panSuccessfulAt, crepSuccessfulAt, emptyPanHooks, emptyCrepHooks,
      panResultOutcome, crepResultOutcome]
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    simp [emptyPanHooks] at hsource
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    simp [emptyPanHooks] at hsource

def emptyPanLub : PanLprefixLub
    (fun clock => panResultEvents (emptyPanHooks.evaluate clock)) :=
  { trace := fun _ => none
    isLub := by
      constructor
      · intro clock index value hvalue
        simp [emptyPanHooks, panResultEvents] at hvalue
      · intro candidate hbound index value htrace
        simp at htrace }

def emptyCrepLub : CrepLprefixLub
    (fun clock => emptyCrepHooks.ioEvents (emptyCrepHooks.evaluate clock).2) :=
  { trace := fun _ => none
    isLub := by
      constructor
      · intro clock index value hvalue
        simp [emptyCrepHooks] at hvalue
      · intro candidate hbound index value htrace
        simp at htrace }

theorem emptySemanticFailure :
    panCrepBehaviourRel
      (panSemanticsWithLub emptyPanHooks emptyPanLub)
      (crepSemanticsWithLub emptyCrepHooks emptyCrepLub) := by
  apply panSemanticsWithLub_rel_crepSemanticsWithLub
    emptyPanHooks emptyCrepHooks emptySemanticAgreement emptyPanLub emptyCrepLub
  rfl

end Flapjack.Test.PanToCrepSemantics
