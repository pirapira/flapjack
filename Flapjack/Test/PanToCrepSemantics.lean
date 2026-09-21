import Flapjack.PanToCrepSemantics
import Flapjack.PanCrepSemanticAgreement

namespace Flapjack.Test.PanToCrepSemantics

open Flapjack

#check @panCrepSemanticAgreement_of_pcCompileCorrect_witnesses

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

/-! The compiler result relation feeds the semantic outcome relation without
    losing the success constructor.  State/value correctness is intentionally
    a premise here, exactly as it is in the full `pc_compile_correct` lift. -/
example {α : Type} (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (targetState : CrepState α)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory [])
      (.returned targetState [])) :
    panCrepSemanticOutcomeRel .success .success := by
  simpa [panValuePcResultOutcome, crepPcResultOutcome] using
    (panValuePcResultRel_semanticOutcomeRel structs context exceptionRel
      exceptionCode globalsLookup
      (.returned sourceLocals sourceGlobals sourceMemory [])
      (.returned targetState []) .success .success hrel rfl rfl)

/-! The same-clock semantic lift also covers a terminal-FFI observation, which
    the no-final-FFI success hypotheses cannot reach. -/
example (event : FfiFinalEvent) :
    panCrepSemanticOutcomeRel (.ffi event.outcome) (.ffi event.outcome) := by
  exact panValuePcResultRel_semanticOutcomeRel_of_outcome
    (structs := [])
    (context := { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 })
    (exceptionRel := fun _ _ _ => True) (exceptionCode := fun _ => none)
    (globalsLookup := fun _ _ => none)
    (panHooks := { evaluate := fun _ => none, ffiOutcome := fun e => e.outcome })
    (hffiOutcome := fun _ => rfl)
    (outcome := .control (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
      { oracle := fun _ _ _ _ => .final .failed, state := (), ioEvents := [] } event))
    (crepResult := .finalFfi { locals := fun _ => none, memory := fun _ => none } event)
    (returnedClock := 0)
    (sourceOutcome := .ffi event.outcome) (targetOutcome := .ffi event.outcome)
    (hrel := by
      simp only [panValuePcResultRel, panOutcomeToPcResult, crepControlToPcResult]
      constructor
      · simp only [panValueCrepStateRel]
        constructor
        · trivial
        · constructor
          · intro name value shape slots hsource _
            simp at hsource
          · funext address
            simp [panValueWordMemory]
      · trivial)
    (hsource := rfl) (htarget := rfl)

end Flapjack.Test.PanToCrepSemantics
