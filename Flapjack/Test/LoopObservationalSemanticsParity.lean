import Flapjack.LoopObservationalSemantics

/-!
# Source parity for `loopSem$semantics`

The source reference is `loopSemScript.sml:508-532`.  The direct HOL fixture
records the clock-zero timeout and clock-one successful entry-call outcomes
for the same `Call NONE (SOME 1) [] NONE` shape.  The Lean checks then exercise
all three observational branches: forbidden result -> `Fail`, a successful
`Result` witness -> `Terminate Success`, and timeout-only runs -> `Diverge`
with the complete clock-indexed I/O-prefix family.  HOL-EVAL leaves the
top-level `semantics` equation symbolic because it contains Hilbert choice
over all clocks; the finite clock observations are therefore the direct HOL
comparison, while the branch/LUB equations are proved in Lean.
-/

namespace Flapjack.Test.LoopObservationalSemanticsParity

open Flapjack

def emptyState (clock : Nat) : LoopMachineState LoopWordLoc :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := clock
    code := []
    be := false
    ffi := .word 0
    baseAddr := .word 4
    topAddr := .word 100 }

def noEvents : LoopMachineState LoopWordLoc → List FfiEvent := fun _ => []

def emptyLprefixLub : LoopLprefixLub (fun _ : Nat => ([] : List FfiEvent)) :=
  { trace := fun _ => none
    isLub := by
      constructor
      · intro _clock index value hvalue
        simp at hvalue
      · intro _candidate _hbound index value htrace
        simp at htrace }

def hooksFor (evaluate : Nat → LoopMachineStep) : LoopSemanticsHooks :=
  { evaluate := evaluate
    ioEvents := noEvents
    ffiOutcome := fun _ => .failed }

def successEvaluate (clock : Nat) : LoopMachineStep :=
  let state := emptyState clock
  if clock = 0 then
    (some .timeOut, { state with locals := fun _ => none })
  else
    (some (.result []), { state with clock := clock - 1 })

def forbiddenEvaluate (_clock : Nat) : LoopMachineStep :=
  (some .error, emptyState 0)

def divergingEvaluate (_clock : Nat) : LoopMachineStep :=
  (some .timeOut, emptyState 0)

def finalFfiEvaluate (_clock : Nat) : LoopMachineStep :=
  (some (.finalFfi (.word 9)), emptyState 0)

def observeStep (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Nat :=
  (step.1, step.2.clock)

def sourceClockParity : Bool :=
  observeStep (successEvaluate 0) == (some .timeOut, 0) &&
    observeStep (successEvaluate 1) == (some (.result []), 0)

theorem emptyPrefixLubProof :
    LoopLprefixLubPredicate (fun _ : Nat => ([] : List FfiEvent)) (fun _ => none) := by
  constructor
  · intro _clock index value hvalue
    simp at hvalue
  · intro _candidate _hbound index value htrace
    simp at htrace

theorem successBranch :
    loopHasSuccessfulRun (hooksFor successEvaluate) := by
  refine ⟨1, some (.result []), emptyState 0, .success, ?_, ?_⟩
  · rfl
  · simp [loopResultOutcome]

theorem successNoForbidden :
    ¬ loopHasForbiddenRun (hooksFor successEvaluate) := by
  rintro ⟨clock, hclock⟩
  cases clock with
  | zero =>
      change loopForbiddenResult (successEvaluate 0).1 at hclock
      simp [successEvaluate, loopForbiddenResult] at hclock
  | succ clock =>
      change loopForbiddenResult (successEvaluate (clock + 1)).1 at hclock
      simp [successEvaluate, loopForbiddenResult] at hclock

theorem finalFfiBranch :
    loopHasSuccessfulRun (hooksFor finalFfiEvaluate) := by
  refine ⟨0, some (.finalFfi (.word 9)), emptyState 0, .ffi .failed, ?_, ?_⟩
  · rfl
  · rfl

theorem finalFfiOutcome :
    loopResultOutcome (hooksFor finalFfiEvaluate)
        (some (.finalFfi (.word 9))) = some (.ffi .failed) := by
  rfl

theorem finalFfiNoForbidden :
    ¬ loopHasForbiddenRun (hooksFor finalFfiEvaluate) := by
  rintro ⟨clock, hclock⟩
  change loopForbiddenResult (finalFfiEvaluate clock).1 at hclock
  simp [finalFfiEvaluate, loopForbiddenResult] at hclock

theorem forbiddenBranch :
    loopHasForbiddenRun (hooksFor forbiddenEvaluate) := by
  exact ⟨0, by simp [loopForbiddenResult, hooksFor, forbiddenEvaluate]⟩

theorem divergenceBranch :
    ¬ loopHasForbiddenRun (hooksFor divergingEvaluate) ∧
      ¬ loopHasSuccessfulRun (hooksFor divergingEvaluate) := by
  constructor
  · rintro ⟨clock, hclock⟩
    simp [loopForbiddenResult, hooksFor, divergingEvaluate] at hclock
  · rintro ⟨clock, result, state, outcome, heval, houtcome⟩
    change (some .timeOut, emptyState 0) = (result, state) at heval
    cases heval
    simp [loopResultOutcome] at houtcome

theorem semanticsForbidden :
    loopSemantics (hooksFor forbiddenEvaluate) emptyLprefixLub = .fail := by
  classical
  simp [loopSemantics, forbiddenBranch]

theorem semanticsSuccess :
    loopSemantics (hooksFor successEvaluate) emptyLprefixLub =
      loopChooseTermination (hooksFor successEvaluate) successBranch := by
  classical
  by_cases forbidden : loopHasForbiddenRun (hooksFor successEvaluate)
  · exact (successNoForbidden forbidden).elim
  · by_cases successful : loopHasSuccessfulRun (hooksFor successEvaluate)
    · simp [loopSemantics, forbidden, successful]
    · exact (successful successBranch).elim

theorem semanticsFinalFfi :
    loopSemantics (hooksFor finalFfiEvaluate) emptyLprefixLub =
      loopChooseTermination (hooksFor finalFfiEvaluate) finalFfiBranch := by
  classical
  by_cases forbidden : loopHasForbiddenRun (hooksFor finalFfiEvaluate)
  · exact (finalFfiNoForbidden forbidden).elim
  · by_cases successful : loopHasSuccessfulRun (hooksFor finalFfiEvaluate)
    · simp [loopSemantics, forbidden, successful]
    · exact (successful finalFfiBranch).elim

theorem semanticsDivergence :
    loopSemantics (hooksFor divergingEvaluate) emptyLprefixLub =
      .diverge (fun _ => []) emptyLprefixLub := by
  classical
  by_cases forbidden : loopHasForbiddenRun (hooksFor divergingEvaluate)
  · exact (divergenceBranch.1 forbidden).elim
  · by_cases successful : loopHasSuccessfulRun (hooksFor divergingEvaluate)
    · exact (divergenceBranch.2 successful).elim
    · simp only [loopSemantics, dif_neg forbidden, dif_neg successful]
      congr 2

#guard sourceClockParity

def runChecks : IO Bool := do
  if sourceClockParity then
    IO.println "PASS semantics source clock observations"
  else
    IO.println "FAIL semantics source clock observations"
  IO.println "PASS semantics source branch proofs"
  pure sourceClockParity

end Flapjack.Test.LoopObservationalSemanticsParity
