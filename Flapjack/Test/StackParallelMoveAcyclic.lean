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

end Flapjack.RiscV
