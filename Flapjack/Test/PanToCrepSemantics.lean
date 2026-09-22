import Flapjack.PanToCrepSemantics
import Flapjack.PanCrepSemanticAgreement

namespace Flapjack.Test.PanToCrepSemantics

open Flapjack

#check @panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock
#check @panCrepSemanticAgreement_of_pcResultRel_pair_cross_clock
#check @Flapjack.PanValuePcSemanticClockEvidence
#check @Flapjack.PanValuePcSemanticClockEvidence.resultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossResultRel_withContextCode
#check @Flapjack.PanValuePcSemanticClockEvidence.returnedSemanticOutcomeRel
#check @Flapjack.PanValuePcSemanticClockEvidence.resultRelWithContextCode
#check @Flapjack.PanValuePcSemanticClockEvidence.normalOrRaisedResultRelWithContextCode_of_branch
#check @Flapjack.PanValuePcSemanticClockEvidence.forbiddenResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.finalFfiSemanticOutcomeRel
#check @Flapjack.PanValuePcSemanticClockEvidence.raisedForbiddenResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.normalForbiddenResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockRaisedForbiddenResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_withContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockRaisedResultRel_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockRaisedResultRelWithContextCode_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalForbiddenResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockReturnedSemanticOutcomeRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockReturnedResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockReturnedResultRel_withContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockReturnedResultRelWithContextCode_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockFinalFfiResultRelWithContextCode_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalResultRel
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalResultRel_withContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalResultRel_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalResultRelWithContextCode_of_stateRelWithContext
#check @Flapjack.PanValuePcSemanticClockEvidence.crossClockNormalOrRaisedResultRelWithContextCode_of_stateRelWithContext
#check @Flapjack.panValuePcResultRelWithContextCode_of_pairwise_normalOrRaised_evidence
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
#check @Flapjack.panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_normalOrRaised_stateRelWithContext
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrect
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock
#check @Flapjack.panEventPrefix_antisymm
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrect_cross_clock_prefix
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_cross_clock_from_pairwise_evidence
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_pairwise_evidence
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_branch_evidence
#check @Flapjack.panCrepSemanticAgreement_of_pcCompileCorrectWithContextCode_normal_call_evidence
#check @Flapjack.panLprefixChain_of_panSemEvaluate_event_prefix
#check @Flapjack.panLprefixChain_of_panSemEvaluate_nonTimeout

example : panEventPrefix ([1] : List Nat) [1, 2] := by
  exact ⟨[2], rfl⟩

example {left right : List Nat} (hleft : panEventPrefix left right)
    (hright : panEventPrefix right left) : left = right := by
  exact panEventPrefix_antisymm hleft hright

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

example (event : FfiFinalEvent) :
    panCrepSemanticOutcomeRel (.ffi event.outcome) (.ffi event.outcome) := by
  let sourceFfi : FfiState Nat :=
    { oracle := fun _ _ _ _ => .final .failed, state := 0, ioEvents := [] }
  let sourceHooks : PanSemanticsHooks Nat Nat :=
    { evaluate := fun _ =>
        some (.control (.finalFfi (fun _ => none) (fun _ => none)
          (fun _ => none) sourceFfi event), 0)
      ffiOutcome := fun e => e.outcome }
  let targetState : CrepState Nat :=
    { locals := fun _ => none, memory := fun _ => none }
  let targetHooks : CrepSemanticsHooks Nat :=
    { evaluate := fun _ =>
        (crepControlResultToSemantic
          (some (.finalFfi targetState event)), targetState)
      ioEvents := fun _ => [] }
  apply panCrepSemanticOutcomeRel_of_pcResultRel_cross_clock
    (structs := [])
    (context := { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 })
    (exceptionRel := fun _ _ _ => True) (exceptionCode := fun _ => none)
    (globalsLookup := fun _ _ => none)
    (panHooks := sourceHooks) (crepHooks := targetHooks)
    (hffiOutcome := by intro e; rfl)
    (sourceClock := 1) (targetClock := 2)
    (sourceOutcome := .control (.finalFfi (fun _ => none) (fun _ => none)
      (fun _ => none) sourceFfi event))
    (returnedClock := 0)
    (targetResult := .finalFfi targetState event)
    (targetState := targetState)
    (sourceSemanticOutcome := .ffi event.outcome)
    (targetSemanticOutcome := .ffi event.outcome)
    (_hsource := by simp [sourceHooks])
    (_htarget := by simp [targetHooks])
    (hrel := by
      simp only [panValuePcResultRel, panOutcomeToPcResult,
        crepControlToPcResult]
      constructor
      · simp only [panValueCrepStateRel]
        constructor
        · trivial
        · constructor
          · intro name value shape slots hsource _
            simp at hsource
          · funext address
            simp [targetState, panValueWordMemory]
      · trivial)
    (hsourceOutcome := by simp [sourceHooks, panResultOutcome])
    (htargetOutcome := by simp [crepControlResultToSemantic,
      crepResultOutcome])

/-! The outcome projections are characterised exactly on the successful
    constructors, which is what the top-level transport cases on. -/
example :
    panValuePcResultOutcome
        (.returned (fun _ => none) (fun _ => none) (fun _ => none) [] :
          PanValuePcResult Nat) = some .success := by
  rw [panValuePcResultOutcome_eq_some_iff]
  exact Or.inl ⟨_, _, _, _, rfl, rfl⟩

example :
    panValuePcResultOutcome
        (.timeout (fun _ => none) (fun _ => none) (fun _ => none) :
          PanValuePcResult Nat) = none := by
  simp [panValuePcResultOutcome]

example :
    crepPcResultOutcome
        (.finalFfi { locals := fun _ => none, memory := fun _ => none }
          { name := .extCall "f", configuration := [], bytes := [],
            outcome := .failed } : CrepPcResult Nat) = some (.ffi .failed) := by
  rw [crepPcResultOutcome_eq_some_iff]
  exact Or.inr ⟨_, _, rfl, rfl⟩

example :
    crepPcResultOutcome
        (.broke { locals := fun _ => none, memory := fun _ => none } 0 :
          CrepPcResult Nat) = none := by
  simp [crepPcResultOutcome]

/-! The forbidden-result bridge is the evaluator/state-relation composition
    used by Cake's normal, raised, and timeout induction branches. -/
example {α σ : Type} [BEq α] [OfNat α 0] [Add α]
    {structs : StructContext} {context : CompileContext α}
    {program : Prog α}
    {sourceEvaluate : PanValuePcEvaluator α}
    {targetEvaluate : CrepPcEvaluator α}
    {codeRel : PanValuePcCodeRel α}
    {excpRel : PanValuePcExceptionShapeRel α}
    {exceptionRel : ExceptionId → PanValue α → α → Prop}
    {exceptionCode : ExceptionId → Option α}
    {globalsLookup : CrepState α → PanValue α → Option (List α)}
    {panHooks : PanSemanticsHooks α σ}
    {crepHooks : CrepSemanticsHooks α}
    (hcorrect : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (evidenceClock : Nat)
    (evidence : PanValuePcSemanticClockEvidence structs context program evidenceClock
      sourceEvaluate targetEvaluate codeRel excpRel exceptionRel exceptionCode
      globalsLookup panHooks crepHooks) :
    panForbiddenResult
        (some (evidence.outcome, evidence.returnedClock)) ↔
      crepForbiddenResult
        (crepControlResultToSemantic (some evidence.result)) := by
  exact PanValuePcSemanticClockEvidence.forbiddenResultRel hcorrect
    evidenceClock evidence

#check @panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_pairwise_evidence
#check @panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_evidence

#check @PanValuePcSemanticClockEvidence.crossClockFinalFfiSemanticOutcomeRel

#check @panValuePcResultRelWithContextCode_of_pairwise_normalOrRaised_evidence

#check @panCrepBehaviourRel_of_pcCompileCorrectWithContextCode_cross_clock_prefix_from_pairwise_stateRelWithContext

end Flapjack.Test.PanToCrepSemantics
