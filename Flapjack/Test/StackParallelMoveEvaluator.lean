import Flapjack.RiscV.CorrectnessStackParallelMoveEvaluator

/-! Regression for the evaluator-facing acyclic parallel-move contract. -/

namespace Flapjack.RiscV

example [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (moves : List (WordLocation × WordLocation)) (other : WordLocation)
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch)
    (hotherDestination : other ∉ moves.map Prod.fst)
    (hotherScratch : other ≠ .register config.scratch)
    (heval : (wordStackParallelLocationMove config moves).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final other =
      wordStackLocationValue config state other := by
  exact evalWordStackMachine_parallelLocationMove_acyclic_preserves_other_value
    config state final moves other hdestinations hnoSource hreserved
    hotherDestination hotherScratch heval

example [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (moves : List (WordLocation × WordLocation))
    (target : WordLocation × WordLocation)
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch)
    (htarget : target ∈ moves)
    (heval : (wordStackParallelLocationMove config moves).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final target.1 =
      wordStackLocationValue config state target.2 := by
  exact evalWordStackMachine_parallelLocationMove_acyclic_preserves_move_value
    config state final moves target hdestinations hnoSource hreserved htarget heval

end Flapjack.RiscV
