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

/-! The outcome projection is non-`none` exactly on the two successful result
    shapes.  These inversions let the top-level transport case on a
    `pc_compile_correct` result without re-unfolding the projection. -/
theorem panValuePcResultOutcome_eq_some_iff (result : PanValuePcResult α)
    (outcome : PanSemanticOutcome) :
    panValuePcResultOutcome result = some outcome ↔
      (∃ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (values : List (PanValue α)),
        result = .returned locals globals memory values ∧ outcome = .success) ∨
      (∃ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (event : FfiFinalEvent),
        result = .finalFfi locals globals memory event ∧
          outcome = .ffi event.outcome) := by
  constructor
  · intro h
    cases result with
    | returned locals globals memory values =>
        exact Or.inl ⟨locals, globals, memory, values, rfl,
          (Option.some.inj h).symm⟩
    | finalFfi locals globals memory event =>
        exact Or.inr ⟨locals, globals, memory, event, rfl,
          (Option.some.inj h).symm⟩
    | error => simp [panValuePcResultOutcome] at h
    | normal locals globals memory => simp [panValuePcResultOutcome] at h
    | raised locals globals memory exception value =>
        simp [panValuePcResultOutcome] at h
    | broke locals globals memory => simp [panValuePcResultOutcome] at h
    | continued locals globals memory => simp [panValuePcResultOutcome] at h
    | timeout locals globals memory => simp [panValuePcResultOutcome] at h
  · intro h
    rcases h with
      ⟨locals, globals, memory, values, rfl, rfl⟩ |
      ⟨locals, globals, memory, event, rfl, rfl⟩ <;> rfl

theorem crepPcResultOutcome_eq_some_iff (result : CrepPcResult α)
    (outcome : CrepSemanticOutcome) :
    crepPcResultOutcome result = some outcome ↔
      (∃ (state : CrepState α) (values : List α),
        result = .returned state values ∧ outcome = .success) ∨
      (∃ (state : CrepState α) (event : FfiFinalEvent),
        result = .finalFfi state event ∧ outcome = .ffi event.outcome) := by
  constructor
  · intro h
    cases result with
    | returned state values =>
        exact Or.inl ⟨state, values, rfl, (Option.some.inj h).symm⟩
    | finalFfi state event =>
        exact Or.inr ⟨state, event, rfl, (Option.some.inj h).symm⟩
    | error => simp [crepPcResultOutcome] at h
    | normal state => simp [crepPcResultOutcome] at h
    | raised state exception => simp [crepPcResultOutcome] at h
    | broke state label => simp [crepPcResultOutcome] at h
    | continued state label => simp [crepPcResultOutcome] at h
    | timeout state => simp [crepPcResultOutcome] at h
  · intro h
    rcases h with
      ⟨state, values, rfl, rfl⟩ |
      ⟨state, event, rfl, rfl⟩ <;> rfl

theorem panValuePcResultOutcome_eq_none_iff (result : PanValuePcResult α) :
    panValuePcResultOutcome result = none ↔
      (∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (values : List (PanValue α)),
        result ≠ .returned locals globals memory values) ∧
      (∀ (locals globals : VarName → Option (PanValue α))
        (memory : α → Option (PanValue α)) (event : FfiFinalEvent),
        result ≠ .finalFfi locals globals memory event) := by
  cases result <;> simp [panValuePcResultOutcome]

theorem crepPcResultOutcome_eq_none_iff (result : CrepPcResult α) :
    crepPcResultOutcome result = none ↔
      (∀ (state : CrepState α) (values : List α),
        result ≠ .returned state values) ∧
      (∀ (state : CrepState α) (event : FfiFinalEvent),
        result ≠ .finalFfi state event) := by
  cases result <;> simp [crepPcResultOutcome]

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

/-! The source and target chains are the same obligation once semantic
    agreement identifies their event families pointwise.  The HOL proof builds
    both chains from the corresponding evaluator monotonicity lemmas; this
    adapter keeps that argument reusable while requiring only the source chain
    at the semantic boundary. -/
theorem crepLprefixChain_of_panLprefixChain_of_semantic_agreement
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock))) :
    crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2) := by
  have hfamily :
      (fun clock => panResultEvents (panHooks.evaluate clock)) =
        (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2) :=
    funext (fun clock => agreement.eventsAt clock)
  simpa [crepLprefixChain, hfamily] using panChain

/-! Reverse the chain transport when the target evaluator provides the
    monotonicity witness first.  This keeps the original HOL prefix-LUB
    obligation symmetric and lets production callers choose either evaluator
    as the source of the chain. -/
theorem panLprefixChain_of_crepLprefixChain_of_semantic_agreement
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock)) := by
  have hfamily :
      (fun clock => panResultEvents (panHooks.evaluate clock)) =
        (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2) :=
    funext (fun clock => agreement.eventsAt clock)
  simpa [panLprefixChain, crepLprefixChain, hfamily] using crepChain

theorem panSemantics_rel_crepSemantics_of_crep_chain
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (crepChain : crepLprefixChain
      (fun clock => crepHooks.ioEvents (crepHooks.evaluate clock).2)) :
    panCrepBehaviourRel
      (panSemantics panHooks
        (panLprefixChain_of_crepLprefixChain_of_semantic_agreement
          panHooks crepHooks agreement crepChain))
      (crepSemantics crepHooks crepChain) := by
  exact panSemantics_rel_crepSemantics panHooks crepHooks agreement
    (panLprefixChain_of_crepLprefixChain_of_semantic_agreement
      panHooks crepHooks agreement crepChain) crepChain

theorem panSemantics_rel_crepSemantics_of_pan_chain
    (panHooks : PanSemanticsHooks α σ)
    (crepHooks : CrepSemanticsHooks β)
    (agreement : PanCrepSemanticAgreement panHooks crepHooks)
    (panChain : panLprefixChain
      (fun clock => panResultEvents (panHooks.evaluate clock))) :
    panCrepBehaviourRel
      (panSemantics panHooks panChain)
      (crepSemantics crepHooks
        (crepLprefixChain_of_panLprefixChain_of_semantic_agreement
          panHooks crepHooks agreement panChain)) := by
  exact panSemantics_rel_crepSemantics panHooks crepHooks agreement panChain
    (crepLprefixChain_of_panLprefixChain_of_semantic_agreement
      panHooks crepHooks agreement panChain)

end Flapjack
