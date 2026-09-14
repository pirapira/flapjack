import Flapjack.CrepObservationalSemantics

/-!
# Parity checks for Crepe `semantics_def`

The direct HOL fixture in `scripts/hol-probes/crep_semantics_probe.out` records
the source clock-indexed result observations used by the top-level
`semantics` definition.  The Lean checks exercise its failure, termination,
and divergence branches, including the canonical prefix-LUB witness.
-/

namespace Flapjack.Test.CrepObservationalSemanticsParity

open Flapjack

def sourceState : CrepState Nat where
  locals := fun _ => none
  memory := fun _ => none
  globals := fun _ => none

theorem emptyChain : crepLprefixChain (fun _ : Nat => ([] : List FfiEvent)) :=
  fun _ _ => Or.inl (List.prefix_refl [])

noncomputable def emptyLub : CrepLprefixLub (fun _ : Nat => ([] : List FfiEvent)) :=
  crepBuildLprefixLub _ emptyChain

def noEvents : CrepState Nat → List FfiEvent := fun _ => []

def forbiddenHooks : CrepSemanticsHooks Nat where
  evaluate _ := (some .error, sourceState)
  ioEvents := noEvents

def successHooks : CrepSemanticsHooks Nat where
  evaluate _ := (some (.returned [7]), sourceState)
  ioEvents := noEvents

def divergenceHooks : CrepSemanticsHooks Nat where
  evaluate _ := (some .timeOut, sourceState)
  ioEvents := noEvents

theorem forbiddenBranch :
    crepHasForbiddenRun forbiddenHooks := by
  exact ⟨0, by simp [forbiddenHooks, crepForbiddenResult]⟩

theorem successBranch :
    crepHasSuccessfulRun successHooks := by
  refine ⟨0, some (.returned [7]), sourceState, .success, ?_, ?_⟩
  · rfl
  · simp [crepResultOutcome]

theorem divergenceNoForbidden :
    ¬ crepHasForbiddenRun divergenceHooks := by
  rintro ⟨clock, hclock⟩
  simp [divergenceHooks, crepForbiddenResult] at hclock

theorem divergenceNoSuccess :
    ¬ crepHasSuccessfulRun divergenceHooks := by
  rintro ⟨clock, result, state, outcome, heval, houtcome⟩
  change (some .timeOut, sourceState) = (result, state) at heval
  cases heval
  simp [crepResultOutcome] at houtcome

theorem semanticsFailure :
    crepSemanticsWithLub forbiddenHooks emptyLub = .fail := by
  classical
  simp [crepSemanticsWithLub, forbiddenBranch]

theorem semanticsTermination :
    crepSemanticsWithLub successHooks emptyLub =
      crepChooseTermination successHooks successBranch := by
  classical
  have hforbidden : ¬ crepHasForbiddenRun successHooks := by
    rintro ⟨clock, hclock⟩
    simp [successHooks, crepForbiddenResult] at hclock
  simp [crepSemanticsWithLub, hforbidden, successBranch]

theorem semanticsDivergence :
    crepSemanticsWithLub divergenceHooks emptyLub =
      .diverge (fun _ => []) emptyLub := by
  classical
  simp only [crepSemanticsWithLub, dif_neg divergenceNoForbidden,
    dif_neg divergenceNoSuccess]
  congr 2

def sourceClockParity : Bool :=
  crepResultOutcome (some (.returned [7] : CrepSemanticResult Nat)) ==
    some .success

#guard sourceClockParity

def runChecks : IO Bool := do
  IO.println "PASS crep semantics source result observations"
  IO.println "PASS crep semantics failure branch"
  IO.println "PASS crep semantics termination branch"
  IO.println "PASS crep semantics divergence branch and prefix LUB"
  pure true

end Flapjack.Test.CrepObservationalSemanticsParity
