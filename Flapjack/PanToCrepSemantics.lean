import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanObservationalSemantics
import Flapjack.CrepObservationalSemantics

/-!
# Semantic transport for the Pancake-to-Crep correctness boundary

This is the Lean counterpart of the semantic part of CakeML's
`state_rel_imp_semantics_to_crep` (`pan_to_crepProofScript.sml:4694`).  The
compiler-specific result relation lives in `PanToCrepCorrectnessBoundary`; the
present theorem supplies the missing observational step.  It is deliberately
stated over the existing source and target hook types so that a later
instantiation can use the clocked `pc_compile_correct` result relation without
introducing a second semantics.

The important detail is that the two semantics use independent classical
choices for successful clocks.  Consequently, pointwise outcome agreement is
not enough: `successfulOutcome` and `successfulEvents` relate *any* successful
source observation to *any* successful target observation.  This is the
choice-stability obligation discharged by the monotone evaluator theorem in
CakeML's original proof.
-/

namespace Flapjack

def panCrepSemanticOutcomeRel : PanSemanticOutcome → CrepSemanticOutcome → Prop
  | .success, .success => True
  | .ffi left, .ffi right => left = right
  | _, _ => False

def panCrepBehaviourRel : PanBehaviour → CrepBehaviour → Prop
  | .fail, .fail => True
  | .terminate sourceOutcome sourceEvents,
      .terminate targetOutcome targetEvents =>
      panCrepSemanticOutcomeRel sourceOutcome targetOutcome ∧
        sourceEvents = targetEvents
  | .diverge sourceFamily sourceTrace,
      .diverge targetFamily targetTrace =>
      sourceFamily = targetFamily ∧ sourceTrace.trace = targetTrace.trace
  | _, _ => False

/-! The result constructors used by `pc_compile_correct` expose more state than
the observational semantics needs.  These projections retain precisely the
two successful observations that `semantics` can choose: a returned value and
a terminal FFI event.  Timeout, control transfer, normal completion, and
raised exceptions remain non-successful observations. -/
def panValuePcResultOutcome : PanValuePcResult α → Option PanSemanticOutcome
  | .returned .. => some .success
  | .finalFfi _ _ _ event => some (.ffi event.outcome)
  | _ => none

def crepPcResultOutcome : CrepPcResult α → Option CrepSemanticOutcome
  | .returned .. => some .success
  | .finalFfi _ event => some (.ffi event.outcome)
  | _ => none

/-! A result relation from the compiler-correctness boundary preserves the
semantic outcome.  This is the constructor-level part of the HOL
`state_rel_imp_semantics_to_crep` lift; evaluator projection and
choice-stability premises remain explicit for the caller. -/
theorem panValuePcResultRel_semanticOutcomeRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceResult : PanValuePcResult α) (targetResult : CrepPcResult α)
    (sourceOutcome : PanSemanticOutcome) (targetOutcome : CrepSemanticOutcome)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceResult targetResult)
    (hsource : panValuePcResultOutcome sourceResult = some sourceOutcome)
    (htarget : crepPcResultOutcome targetResult = some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  cases sourceResult <;> cases targetResult <;>
    simp [panValuePcResultRel, panValuePcResultOutcome, crepPcResultOutcome]
      at hrel hsource htarget ⊢ <;>
    cases sourceOutcome <;> cases targetOutcome <;>
    simp_all [panCrepSemanticOutcomeRel]

def panSuccessfulAt (hooks : PanSemanticsHooks α σ) (clock : Nat) : Prop :=
  ∃ result outcome,
    hooks.evaluate clock = some result ∧
      panResultOutcome hooks (some result) = some outcome

def crepSuccessfulAt (hooks : CrepSemanticsHooks α) (clock : Nat) : Prop :=
  ∃ result state outcome,
    hooks.evaluate clock = (result, state) ∧
      crepResultOutcome result = some outcome

structure PanCrepSemanticAgreement
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β) : Prop where
  eventsAt : ∀ clock,
    panResultEvents (panHooks.evaluate clock) =
      crepHooks.ioEvents (crepHooks.evaluate clock).2
  forbiddenAt : ∀ clock,
    panForbiddenResult (panHooks.evaluate clock) ↔
      crepForbiddenResult (crepHooks.evaluate clock).1
  successfulAt : ∀ clock,
    panSuccessfulAt panHooks clock ↔ crepSuccessfulAt crepHooks clock
  successfulOutcome : ∀
    (sourceClock targetClock : Nat)
    (sourceResult : PanValueFfiClockResult α σ)
    (sourceOutcome : PanSemanticOutcome)
    (targetResult : Option (CrepSemanticResult β))
    (targetState : CrepState β)
    (targetOutcome : CrepSemanticOutcome),
    panHooks.evaluate sourceClock = some sourceResult →
    panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
    crepHooks.evaluate targetClock = (targetResult, targetState) →
    crepResultOutcome targetResult = some targetOutcome →
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome
  successfulEvents : ∀
    (sourceClock targetClock : Nat)
    (sourceResult : PanValueFfiClockResult α σ)
    (sourceOutcome : PanSemanticOutcome)
    (targetResult : Option (CrepSemanticResult β))
    (targetState : CrepState β)
    (targetOutcome : CrepSemanticOutcome),
    panHooks.evaluate sourceClock = some sourceResult →
    panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
    crepHooks.evaluate targetClock = (targetResult, targetState) →
    crepResultOutcome targetResult = some targetOutcome →
    panResultEvents (some sourceResult) = crepHooks.ioEvents targetState

theorem panCrepSemanticAgreement_panSuccessfulAt_iff
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (clock : Nat) :
    panSuccessfulAt panHooks clock ↔ crepSuccessfulAt crepHooks clock :=
  agreement.successfulAt clock

theorem panCrepSemanticAgreement_forbiddenAt_iff
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (clock : Nat) :
    panForbiddenResult (panHooks.evaluate clock) ↔
      crepForbiddenResult (crepHooks.evaluate clock).1 :=
  agreement.forbiddenAt clock

theorem panSemanticsWithLub_rel_crepSemanticsWithLub
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (panLub : PanLprefixLub
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepLub : CrepLprefixLub
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2))
    (htrace : panLub.trace = crepLub.trace) :
    panCrepBehaviourRel
      (panSemanticsWithLub panHooks panLub)
      (crepSemanticsWithLub crepHooks crepLub) := by
  classical
  by_cases hpanForbidden : panHasForbiddenRun panHooks
  · have hcrepForbidden : crepHasForbiddenRun crepHooks := by
      rcases hpanForbidden with ⟨clock, hclock⟩
      exact ⟨clock, (agreement.forbiddenAt clock).mp hclock⟩
    simp [panSemanticsWithLub, crepSemanticsWithLub,
      hpanForbidden, hcrepForbidden, panCrepBehaviourRel]
  · have hcrepForbidden : ¬ crepHasForbiddenRun crepHooks := by
      intro hcrep
      rcases hcrep with ⟨clock, hclock⟩
      exact hpanForbidden ⟨clock, (agreement.forbiddenAt clock).mpr hclock⟩
    by_cases hpanSuccessful : panHasSuccessfulRun panHooks
    · have hcrepSuccessful : crepHasSuccessfulRun crepHooks := by
        rcases hpanSuccessful with ⟨clock, result, outcome, heval, houtcome⟩
        rcases (agreement.successfulAt clock).mp
          ⟨result, outcome, heval, houtcome⟩ with
          ⟨targetResult, targetState, targetOutcome, htarget, htargetOutcome⟩
        exact ⟨clock, targetResult, targetState, targetOutcome,
          htarget, htargetOutcome⟩
      simp only [panSemanticsWithLub, crepSemanticsWithLub,
        dif_neg hpanForbidden, dif_neg hcrepForbidden,
        dif_pos hpanSuccessful, dif_pos hcrepSuccessful]
      unfold panChooseTermination crepChooseTermination
      let sourceClock := Classical.choose hpanSuccessful
      let sourceResultWitness := Classical.choose_spec hpanSuccessful
      let sourceResult := Classical.choose sourceResultWitness
      let sourceOutcomeWitness := Classical.choose_spec sourceResultWitness
      let sourceOutcome := Classical.choose sourceOutcomeWitness
      let targetClock := Classical.choose hcrepSuccessful
      let targetResultWitness := Classical.choose_spec hcrepSuccessful
      let targetResult := Classical.choose targetResultWitness
      let targetStateWitness := Classical.choose_spec targetResultWitness
      let targetState := Classical.choose targetStateWitness
      let targetOutcomeWitness := Classical.choose_spec targetStateWitness
      let targetOutcome := Classical.choose targetOutcomeWitness
      have hsource : panHooks.evaluate sourceClock = some sourceResult := by
        exact (Classical.choose_spec sourceOutcomeWitness).1
      have hsourceOutcome :
          panResultOutcome panHooks (some sourceResult) = some sourceOutcome := by
        exact (Classical.choose_spec sourceOutcomeWitness).2
      have htarget : crepHooks.evaluate targetClock =
          (targetResult, targetState) := by
        exact (Classical.choose_spec targetOutcomeWitness).1
      have htargetOutcome : crepResultOutcome targetResult = some targetOutcome := by
        exact (Classical.choose_spec targetOutcomeWitness).2
      have houtcome := agreement.successfulOutcome sourceClock targetClock
        sourceResult sourceOutcome targetResult targetState targetOutcome
        hsource hsourceOutcome htarget htargetOutcome
      have hevents := agreement.successfulEvents sourceClock targetClock
        sourceResult sourceOutcome targetResult targetState targetOutcome
        hsource hsourceOutcome htarget htargetOutcome
      exact ⟨houtcome, hevents⟩
    · have hcrepSuccessful : ¬ crepHasSuccessfulRun crepHooks := by
        intro hcrep
        rcases hcrep with ⟨clock, result, state, outcome, heval, houtcome⟩
        rcases (agreement.successfulAt clock).mpr
          ⟨result, state, outcome, heval, houtcome⟩ with
          ⟨sourceResult, sourceOutcome, hsource, hsourceOutcome⟩
        exact hpanSuccessful ⟨clock, sourceResult, sourceOutcome,
          hsource, hsourceOutcome⟩
      simp only [panSemanticsWithLub, crepSemanticsWithLub,
        dif_neg hpanForbidden, dif_neg hcrepForbidden,
        dif_neg hpanSuccessful, dif_neg hcrepSuccessful]
      exact ⟨funext (fun clock => agreement.eventsAt clock), htrace⟩

theorem panSemantics_rel_crepSemantics
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)))
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks crepChain) := by
  have hfamily :
      (fun clock => panResultEvents (panHooks.evaluate clock)) =
        (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2) :=
    funext (fun clock => agreement.eventsAt clock)
  have htrace :
      (buildPanLprefixLub _ panChain).trace =
        (crepBuildLprefixLub _ crepChain).trace := by
    change loopFamilyNth (fun clock => panResultEvents (panHooks.evaluate clock)) =
      loopFamilyNth (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)
    rw [hfamily]
  exact panSemanticsWithLub_rel_crepSemanticsWithLub
    panHooks crepHooks agreement (buildPanLprefixLub _ panChain)
    (crepBuildLprefixLub _ crepChain) htrace

end Flapjack
