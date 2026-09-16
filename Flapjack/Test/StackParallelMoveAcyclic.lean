import Flapjack.RiscV.CorrectnessStackParallelMoveAcyclic

/-! Regression for source-ordered lowering of an acyclic stack move list. -/

namespace Flapjack.RiscV

def acyclicParallelConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    addressScratch := 30
    stackBase := 8 }

example :
    wordStackParallelLocationMove (α := Nat) acyclicParallelConfig
      [(.register 5, .register 2), (.stack 1, .register 4)] =
      wordStackSequentialLocationMove (α := Nat) acyclicParallelConfig
        [(.register 5, .register 2), (.stack 1, .register 4)] := by
  apply wordStackParallelLocationMove_acyclic_eq_sequential
  · simp
  · intro move hmove hsource
    simp at hmove
    rcases hmove with hmove | hmove
    · subst move
      simp at hsource
    · subst move
      simp at hsource
  · intro move hmove
    simp at hmove
    rcases hmove with hmove | hmove
    · subst move
      simp [acyclicParallelConfig]
    · subst move
      simp [acyclicParallelConfig]

/-- The dependency chain `{r3 <- r1, r1 <- r2}` preserves the original `r1`
    by emitting `r3 <- r1` before the move that overwrites `r1`. -/
example :
    wordStackParallelLocationMove (α := Nat) acyclicParallelConfig
      [(.register 3, .register 1), (.register 1, .register 2)] =
      some (.seq (.arith .or 3 1 1) (.arith .or 1 2 2)) := by
  simp [wordStackParallelLocationMove, wordStackParallelLocationMoveAux,
    wordStackLocationMoveDestinations, wordStackLocationMoveReady,
    wordStackLocationMoveRemoveDestination, wordStackLocationMove,
    wordStackJoin, acyclicParallelConfig]

/-- A two-cycle still goes through the reserved address-scratch register and
    restores the postponed destination. -/
example :
    wordStackParallelLocationMove (α := Nat) acyclicParallelConfig
      [(.register 1, .register 2), (.register 2, .register 1)] =
      some (.seq (.arith .or 30 2 2)
        (.seq (.arith .or 2 1 1) (.arith .or 1 30 30))) := by
  simp [wordStackParallelLocationMove, wordStackParallelLocationMoveAux,
    wordStackLocationMoveDestinations, wordStackLocationMoveReady,
    wordStackLocationMoveRemoveDestination, wordStackLocationMoveToScratch,
    wordStackLocationMoveFromScratch, wordStackLocationMove,
    wordStackJoin, acyclicParallelConfig]

end Flapjack.RiscV
