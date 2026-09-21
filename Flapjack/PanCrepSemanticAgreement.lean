import Flapjack.PanToCrepSemantics
import Flapjack.PanToCrepCorrectnessBoundary

/-!
# From the clocked `pc_compile_correct` result relation to observational semantics

This module is the semantic counterpart of CakeML's
`state_rel_imp_semantics_to_crep` (`pan_to_crepProofScript.sml:4694`): it turns
the per-clock compiler result relation `panValuePcResultRel` into an
observational-semantics agreement `PanCrepSemanticAgreement`, and then into a
`panCrepBehaviourRel` between the two top-level semantics.

The source semantics observes `Return` and `FinalFFI` witnesses, treats any
other observation as a forbidden run, and otherwise assembles the FFI-event
prefix LUB.  The result relation `panValuePcResultRel` pins the constructor of
the target observation to the source constructor, so the same-clock failure and
success observations transport.  The genuinely cross-clock obligations are the
*choice-stability* obligations of CakeML's original proof; for the no-final-FFI
fragment used below they reduce to "every successful observation is a
`Return`", which is exactly the shape a later `finalFfi`-carrying instantiation
has to strengthen with the monotone-evaluator theorem.
-/

namespace Flapjack

/-! ## Clocked results as compact `pc` results -/

/-- Project a clocked source outcome onto the compact `pc_compile_correct`
source result.  The `finalFfi` control case keeps the event, and `timeout`
becomes the compact `timeout` result. -/
def panOutcomeToPcResult : PanValueFfiClockOutcome α σ → PanValuePcResult α
  | .control (.normal locals globals memory _) => .normal locals globals memory
  | .control (.returned locals globals memory _ values) =>
      .returned locals globals memory values
  | .control (.raised locals globals memory _ exception value) =>
      .raised locals globals memory exception value
  | .control (.broke locals globals memory _) => .broke locals globals memory
  | .control (.continued locals globals memory _) => .continued locals globals memory
  | .control (.finalFfi locals globals memory _ event) =>
      .finalFfi locals globals memory event
  | .timeout locals globals memory _ => .timeout locals globals memory

/-- Project a Crep control result onto the compact `pc_compile_correct` target
result.  Unlike the boundary bridge, `finalFfi` is retained: the observational
semantics treats it as a successful observation. -/
def crepControlToPcResult : CrepControlResult α → CrepPcResult α
  | .normal state => .normal state
  | .returned state values => .returned state values
  | .raised state exception => .raised state exception
  | .broke state label => .broke state label
  | .continued state label => .continued state label
  | .finalFfi state event => .finalFfi state event

/-! ## Same-clock field transport -/

set_option linter.unusedSimpArgs false in
/-- Forbidden-ness transports across `panValuePcResultRel`: the relation never
maps a forbidden observation to a successful one or conversely. -/
theorem panValuePcResultRel_forbidden_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult)) :
    panForbiddenResult (some (outcome, returnedClock)) ↔
      crepForbiddenResult (crepControlResultToSemantic (some crepResult)) := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panForbiddenResult, crepForbiddenResult,
          panValuePcResultRel]
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panForbiddenResult, crepForbiddenResult,
          panValuePcResultRel]

set_option linter.unusedSimpArgs false in
/-- Successful-ness transports across `panValuePcResultRel`. -/
theorem panValuePcResultRel_success_iff
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult)) :
    (∃ sourceOutcome,
        panResultOutcome panHooks (some (outcome, returnedClock)) =
          some sourceOutcome) ↔
      (∃ targetOutcome,
        crepResultOutcome (crepControlResultToSemantic (some crepResult)) =
          some targetOutcome) := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panValuePcResultRel]
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panValuePcResultRel]

set_option linter.unusedSimpArgs false in
/-- Same-clock successful observations relate: a `Return`/`Return` pair is
`success`/`success`, and a `FinalFFI`/`FinalFFI` pair shares the event (hence
the outcome, when the source hook reads `event.outcome`). -/
theorem panValuePcResultRel_success_outcome
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ)
    (hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (outcome : PanValueFfiClockOutcome α σ) (crepResult : CrepControlResult α)
    (returnedClock : Nat) (sourceOutcome : PanSemanticOutcome)
    (targetOutcome : CrepSemanticOutcome)
    (hrel : panValuePcResultRel structs context exceptionRel exceptionCode
      globalsLookup (panOutcomeToPcResult outcome)
      (crepControlToPcResult crepResult))
    (hsource : panResultOutcome panHooks (some (outcome, returnedClock)) =
      some sourceOutcome)
    (htarget : crepResultOutcome (crepControlResultToSemantic (some crepResult)) =
      some targetOutcome) :
    panCrepSemanticOutcomeRel sourceOutcome targetOutcome := by
  cases outcome with
  | control result =>
      cases result <;> cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panCrepSemanticOutcomeRel, panValuePcResultRel, hffiOutcome] <;>
        (try (subst sourceOutcome; subst targetOutcome;
              simp [panCrepSemanticOutcomeRel, hffiOutcome]))
  | timeout locals globals memory ffi =>
      cases crepResult <;>
        simp_all [panOutcomeToPcResult, crepControlToPcResult,
          crepControlResultToSemantic, panResultOutcome, crepResultOutcome,
          panCrepSemanticOutcomeRel, panValuePcResultRel] <;>
        (try (subst sourceOutcome; subst targetOutcome;
              simp [panCrepSemanticOutcomeRel, hffiOutcome]))

/-! ## The agreement from clocked compiler evidence -/

/-- Build a `PanCrepSemanticAgreement` from a per-clock `panValuePcResultRel`
relation between the source and target evaluators.

`hrel` is the `pc_compile_correct` result relation instantiated at each clock;
`hevents` is the FFI-trace component that the relation deliberately does not
carry.  The two `Success` hypotheses are the no-final-FFI choice-stability
obligations: in the no-final-FFI fragment every successful observation is a
`Return`, so the cross-clock outcome fields of the agreement are immediate.
A later `finalFfi`-carrying instantiation replaces them with the
monotone-evaluator theorem. -/
theorem panCrepSemanticAgreement_of_pcResultRel
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ) (crepHooks : CrepSemanticsHooks α)
    (_hffiOutcome : ∀ event, panHooks.ffiOutcome event = event.outcome)
    (hpanEval : ∀ clock, ∃ outcome returnedClock,
      panHooks.evaluate clock = some (outcome, returnedClock))
    (hcrepEval : ∀ clock, ∃ result state,
      crepHooks.evaluate clock =
        (crepControlResultToSemantic (some result), state))
    (hrel : ∀ clock outcome returnedClock result,
      panHooks.evaluate clock = some (outcome, returnedClock) →
      (crepHooks.evaluate clock).1 = crepControlResultToSemantic (some result) →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult outcome) (crepControlToPcResult result))
    (hevents : ∀ clock,
      panResultEvents (panHooks.evaluate clock) =
        crepHooks.ioEvents (crepHooks.evaluate clock).2)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro clock
    exact hevents clock
  · intro clock
    obtain ⟨outcome, returnedClock, hpanClock⟩ := hpanEval clock
    obtain ⟨result, state, hcrepClock⟩ := hcrepEval clock
    rw [hpanClock, hcrepClock]
    exact panValuePcResultRel_forbidden_iff structs context exceptionRel
      exceptionCode globalsLookup outcome result returnedClock
      (hrel clock outcome returnedClock result hpanClock (by rw [hcrepClock]))
  · intro clock
    obtain ⟨outcome, returnedClock, hpanClock⟩ := hpanEval clock
    obtain ⟨result, state, hcrepClock⟩ := hcrepEval clock
    have hpanAt : panSuccessfulAt panHooks clock ↔
        ∃ sourceOutcome,
          panResultOutcome panHooks (some (outcome, returnedClock)) =
            some sourceOutcome := by
      constructor
      · rintro ⟨result', outcome', heval, houtcome⟩
        rw [hpanClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨sourceOutcome, houtcome⟩
        exact ⟨(outcome, returnedClock), sourceOutcome, hpanClock, houtcome⟩
    have hcrepAt : crepSuccessfulAt crepHooks clock ↔
        ∃ targetOutcome,
          crepResultOutcome
            (crepControlResultToSemantic (some result)) = some targetOutcome := by
      constructor
      · rintro ⟨result', state', outcome', heval, houtcome⟩
        rw [hcrepClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨targetOutcome, houtcome⟩
        exact ⟨crepControlResultToSemantic (some result), state, targetOutcome,
          hcrepClock, houtcome⟩
    rw [hpanAt, hcrepAt]
    exact panValuePcResultRel_success_iff structs context exceptionRel
      exceptionCode globalsLookup panHooks outcome result returnedClock
      (hrel clock outcome returnedClock result hpanClock (by rw [hcrepClock]))
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    have hsourceKind := hpanSuccess sourceClock sourceResult sourceOutcome
      hsource hsourceOutcome
    have htargetKind := hcrepSuccess targetClock targetResult targetState
      targetOutcome htarget htargetOutcome
    rw [hsourceKind, htargetKind]
    simp [panCrepSemanticOutcomeRel]
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    rw [hpanSuccessEvents sourceClock sourceResult sourceOutcome hsource
        hsourceOutcome,
      hcrepSuccessEvents targetClock targetResult targetState targetOutcome
        htarget htargetOutcome]


/-! ## The agreement from a per-clock result pair

The theorem above takes the pointwise relation through the *semantic* projection
`crepControlResultToSemantic`, which forgets the target state in the `normal`
case.  The version below instead asks for the raw target `CrepControlResult`
and state, together with the event equality, at each clock.  This is the shape a
concrete compiler instantiation can discharge. -/
theorem panCrepSemanticAgreement_of_pcResultRel_pair
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (panHooks : PanSemanticsHooks α σ) (crepHooks : CrepSemanticsHooks α)
    (hpair : ∀ clock, ∃ (outcome : PanValueFfiClockOutcome α σ)
      (returnedClock : Nat) (result : CrepControlResult α) (state : CrepState α),
      panHooks.evaluate clock = some (outcome, returnedClock) ∧
      crepHooks.evaluate clock =
        (crepControlResultToSemantic (some result), state) ∧
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panOutcomeToPcResult outcome) (crepControlToPcResult result) ∧
      panResultEvents (some (outcome, returnedClock)) = crepHooks.ioEvents state)
    (hpanSuccess : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      sourceOutcome = .success)
    (hcrepSuccess : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      targetOutcome = .success)
    (hpanSuccessEvents : ∀ clock (sourceResult : PanValueFfiClockResult α σ)
      (sourceOutcome : PanSemanticOutcome),
      panHooks.evaluate clock = some sourceResult →
      panResultOutcome panHooks (some sourceResult) = some sourceOutcome →
      panResultEvents (some sourceResult) = [])
    (hcrepSuccessEvents : ∀ clock (targetResult : Option (CrepSemanticResult α))
      (targetState : CrepState α) (targetOutcome : CrepSemanticOutcome),
      crepHooks.evaluate clock = (targetResult, targetState) →
      crepResultOutcome targetResult = some targetOutcome →
      crepHooks.ioEvents targetState = []) :
    PanCrepSemanticAgreement panHooks crepHooks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, _,
      hevents⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact hevents
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    rw [hpanClock, hcrepClock]
    exact panValuePcResultRel_forbidden_iff structs context exceptionRel
      exceptionCode globalsLookup outcome result returnedClock hrel
  · intro clock
    obtain ⟨outcome, returnedClock, result, state, hpanClock, hcrepClock, hrel,
      _⟩ := hpair clock
    have hpanAt : panSuccessfulAt panHooks clock ↔
        ∃ sourceOutcome,
          panResultOutcome panHooks (some (outcome, returnedClock)) =
            some sourceOutcome := by
      constructor
      · rintro ⟨result', outcome', heval, houtcome⟩
        rw [hpanClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨sourceOutcome, houtcome⟩
        exact ⟨(outcome, returnedClock), sourceOutcome, hpanClock, houtcome⟩
    have hcrepAt : crepSuccessfulAt crepHooks clock ↔
        ∃ targetOutcome,
          crepResultOutcome
            (crepControlResultToSemantic (some result)) = some targetOutcome := by
      constructor
      · rintro ⟨result', state', outcome', heval, houtcome⟩
        rw [hcrepClock] at heval
        cases heval
        exact ⟨outcome', houtcome⟩
      · rintro ⟨targetOutcome, houtcome⟩
        exact ⟨crepControlResultToSemantic (some result), state, targetOutcome,
          hcrepClock, houtcome⟩
    rw [hpanAt, hcrepAt]
    exact panValuePcResultRel_success_iff structs context exceptionRel
      exceptionCode globalsLookup panHooks outcome result returnedClock hrel
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    have hsourceKind := hpanSuccess sourceClock sourceResult sourceOutcome
      hsource hsourceOutcome
    have htargetKind := hcrepSuccess targetClock targetResult targetState
      targetOutcome htarget htargetOutcome
    rw [hsourceKind, htargetKind]
    simp [panCrepSemanticOutcomeRel]
  · intro sourceClock targetClock sourceResult sourceOutcome targetResult
      targetState targetOutcome hsource hsourceOutcome htarget htargetOutcome
    rw [hpanSuccessEvents sourceClock sourceResult sourceOutcome hsource
        hsourceOutcome,
      hcrepSuccessEvents targetClock targetResult targetState targetOutcome
        htarget htargetOutcome]

/-! ## A concrete no-final-FFI instantiation

This instantiation has a normal run at clock `0` and a successful returned run at
every positive clock, so the outcome and event fields of
`PanCrepSemanticAgreement` are exercised against a genuine `panValueCrepStateRel`
rather than the vacuous no-run hooks of `Flapjack/Test/PanToCrepSemantics.lean`. -/

def demoFfiState : FfiState Unit where
  oracle := fun _ _ _ _ => .final .failed
  state := ()
  ioEvents := []

def demoPanHooks : PanSemanticsHooks Nat Unit where
  evaluate := fun clock =>
    if clock = 0 then
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        demoFfiState), 0)
    else
      some (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        demoFfiState [PanValue.word 41]), clock)
  ffiOutcome := fun event => event.outcome

def demoCrepState : CrepState Nat where
  locals := fun _ => none
  memory := fun _ => none
  globals := fun _ => none

def demoCrepHooks : CrepSemanticsHooks Nat where
  evaluate := fun clock =>
    if clock = 0 then
      (crepControlResultToSemantic (some (.normal demoCrepState)), demoCrepState)
    else
      (crepControlResultToSemantic (some (.returned demoCrepState [41])),
        demoCrepState)
  ioEvents := fun _ => []

def demoContext : CompileContext Nat where
  vars := []
  functions := []
  exceptions := []
  maxVar := 0
  bytesInWord := 8

theorem demoPanValueCrepStateRel :
    panValueCrepStateRel [] demoContext (fun _ => none) (fun _ => none)
      (fun _ => none) demoCrepState := by
  refine ⟨rfl, ?_, rfl⟩
  intro name value shape slots hsource _
  simp at hsource

set_option linter.unusedSimpArgs false in
theorem demoPanCrepSemanticAgreement :
    PanCrepSemanticAgreement demoPanHooks demoCrepHooks := by
  apply panCrepSemanticAgreement_of_pcResultRel_pair [] demoContext
    (fun _ _ _ => True) (fun _ => none) (fun _ _ => none) demoPanHooks demoCrepHooks
  · intro clock
    by_cases hclock : clock = 0
    · subst hclock
      exact ⟨.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
          demoFfiState), 0, .normal demoCrepState, demoCrepState,
        by simp [demoPanHooks],
        by simp [demoCrepHooks],
        demoPanValueCrepStateRel,
        by simp [demoPanHooks, demoCrepHooks, demoFfiState, panResultEvents,
          panResultFfi]⟩
    · exact ⟨.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
          demoFfiState [PanValue.word 41]), clock, .returned demoCrepState [41],
        demoCrepState,
        by simp [demoPanHooks, hclock],
        by simp [demoCrepHooks, hclock],
        ⟨demoPanValueCrepStateRel,
          by simp [panValueCrepValuesRel, panValueFlatWords, panValueFlatWordsFuel, panValueFlatValueFuel]⟩,
        by simp [demoPanHooks, demoCrepHooks, demoFfiState, hclock,
          panResultEvents, panResultFfi]⟩
  · intro clock sourceResult sourceOutcome hsource houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have hsrc : sourceResult =
          (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState), 0) := by simpa [demoPanHooks] using hsource.symm
      rw [hsrc] at houtcome
      simp only [panResultOutcome] at houtcome
      simp at houtcome
    · have hsrc : sourceResult =
          (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState [PanValue.word 41]), clock) := by
        simpa [demoPanHooks, hclock] using hsource.symm
      rw [hsrc] at houtcome
      simp only [panResultOutcome] at houtcome
      simpa using houtcome.symm
  · intro clock targetResult targetState targetOutcome htarget houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have htgt : targetResult =
          crepControlResultToSemantic (some (.normal demoCrepState)) := by
        simpa [demoCrepHooks] using (congrArg Prod.fst htarget).symm
      rw [htgt] at houtcome
      simp only [crepControlResultToSemantic, crepResultOutcome] at houtcome
      simp at houtcome
    · have htgt : targetResult =
          crepControlResultToSemantic (some (.returned demoCrepState [41])) := by
        simpa [demoCrepHooks, hclock] using (congrArg Prod.fst htarget).symm
      rw [htgt] at houtcome
      simp only [crepControlResultToSemantic, crepResultOutcome] at houtcome
      simpa using houtcome.symm
  · intro clock sourceResult sourceOutcome hsource _houtcome
    by_cases hclock : clock = 0
    · subst hclock
      have hsrc : sourceResult =
          (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState), 0) := by simpa [demoPanHooks] using hsource.symm
      rw [hsrc]
      simp [panResultEvents, panResultFfi, demoFfiState, demoCrepHooks]
    · have hsrc : sourceResult =
          (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
            demoFfiState [PanValue.word 41]), clock) := by
        simpa [demoPanHooks, hclock] using hsource.symm
      rw [hsrc]
      simp [panResultEvents, panResultFfi, demoFfiState, demoCrepHooks]
  · intro clock targetResult targetState targetOutcome _htarget _houtcome
    by_cases hclock : clock = 0
    · subst hclock
      simp [demoCrepHooks]
    · simp [demoCrepHooks, hclock]

end Flapjack
