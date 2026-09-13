import Flapjack.LoopObservationalSemantics

/-!
# Source parity for `loopSem$semantics`

The source reference is `loopSemScript.sml:508-532`.  The direct HOL fixture
records the clock-zero timeout and clock-one successful entry-call outcomes
for the same `Call NONE (SOME 1) [] NONE` shape.  The Lean checks then exercise
all three observational branches: forbidden result -> `Fail`, a successful
`Result` witness -> `Terminate Success`, and timeout-only runs -> `Diverge`
with the complete clock-indexed I/O-prefix family.
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

def observeStep (step : LoopMachineStep) :
    Option (LoopMachineResult LoopWordLoc) × Nat :=
  (step.1, step.2.clock)

def sourceClockParity : Bool :=
  observeStep (successEvaluate 0) == (some .timeOut, 0) &&
    observeStep (successEvaluate 1) == (some (.result []), 0)

theorem successBranch :
    loopHasSuccessfulRun (hooksFor successEvaluate) := by
  refine ⟨1, some (.result []), emptyState 0, .success, ?_, ?_⟩
  · rfl
  · simp [loopResultOutcome]

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

#guard sourceClockParity

def runChecks : IO Bool := do
  if sourceClockParity then
    IO.println "PASS semantics source clock observations"
  else
    IO.println "FAIL semantics source clock observations"
  IO.println "PASS semantics source branch proofs"
  pure sourceClockParity

end Flapjack.Test.LoopObservationalSemanticsParity
