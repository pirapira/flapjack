import Flapjack.RiscV.CorrectnessStackParallelMove

/-!
# Acyclic StackLang parallel moves

For fresh function-entry moves no source is also a destination.  In that
case the scratch-aware scheduler always selects the head move and never takes
its cycle-saving branch.  This file records the resulting executable
equation, leaving the evaluator simulation to consume the simpler sequence.
-/

namespace Flapjack.RiscV

def wordStackSequentialLocationMove (config : WordStackConfig) :
    List (WordLocation × WordLocation) → Option (StackProg α)
  | [] => some .skip
  | (destination, source) :: moves => do
      let first ← wordStackLocationMove config destination source
      let rest ← wordStackSequentialLocationMove config moves
      pure (wordStackJoin first rest)

theorem wordStackParallelLocationMove_acyclic_eq_sequential
    (config : WordStackConfig)
    (moves : List (WordLocation × WordLocation))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch) :
    wordStackParallelLocationMove (α := Nat) config moves =
      wordStackSequentialLocationMove (α := Nat) config moves := by
  induction moves with
  | nil =>
      simp only [wordStackParallelLocationMove,
        wordStackParallelLocationMoveAux]
      simp [wordStackLocationMoveDestinations,
        wordStackSequentialLocationMove]
  | cons head tail ih =>
      have hdestinations' :
          (head.1 :: tail.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hdestinations
      have htailDestinations : (tail.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hdestinations').2
      have htailNoSource : ∀ move, move ∈ tail →
          move.2 ∉ tail.map Prod.fst := by
        intro move hmove hsource
        apply hnoSource move (by simp [hmove])
        simp [hsource]
      have htailReserved : ∀ move, move ∈ tail →
          move.1 ≠ .register config.scratch ∧
          move.1 ≠ .register config.addressScratch ∧
          move.2 ≠ .register config.scratch ∧
          move.2 ≠ .register config.addressScratch := by
        intro move hmove
        exact hreserved move (by simp [hmove])
      have hheadNoSource : head.2 ∉ head.1 :: tail.map Prod.fst := by
        simpa only [List.map_cons] using hnoSource head (by simp)
      have hheadReady :
          wordStackLocationMoveReady (head.1 :: tail.map Prod.fst)
              (head :: tail) = some head := by
        simp [wordStackLocationMoveReady, hheadNoSource]
      have hheadNotTailDestination : ∀ move, move ∈ tail →
          move.1 ≠ head.1 := by
        intro move hmove heq
        apply (List.nodup_cons.mp hdestinations').1
        exact List.mem_map.mpr ⟨move, hmove, heq⟩
      have hremoved :
          wordStackLocationMoveRemoveDestination head.1 (head :: tail) = tail := by
        simp only [wordStackLocationMoveRemoveDestination, List.filter_cons]
        have hhead : (head.1 != head.1) = false := by simp
        rw [hhead]
        have hfilter : ∀ xs : List (WordLocation × WordLocation),
            (∀ move, move ∈ xs → move.1 ≠ head.1) →
            List.filter (fun move => move.1 != head.1) xs = xs := by
          intro xs hxs
          induction xs with
          | nil => rfl
          | cons move xs ihxs =>
              have hmove := hxs move (by simp)
              have htail : ∀ other, other ∈ xs → other.1 ≠ head.1 := by
                intro other hother
                exact hxs other (by simp [hother])
              simp [hmove, ihxs htail]
        exact hfilter tail hheadNotTailDestination
      have hany : (head :: tail).any
          (fun move =>
            (move.1 = .register config.scratch ||
              move.1 = .register config.addressScratch) ||
            (move.2 = .register config.scratch ||
              move.2 = .register config.addressScratch)) = false := by
        have hfalse : ∀ xs : List (WordLocation × WordLocation),
            (∀ move, move ∈ xs →
              ((move.1 = .register config.scratch ||
                move.1 = .register config.addressScratch) ||
               (move.2 = .register config.scratch ||
                move.2 = .register config.addressScratch)) = false) →
            xs.any (fun move =>
              (move.1 = .register config.scratch ||
                move.1 = .register config.addressScratch) ||
              (move.2 = .register config.scratch ||
                move.2 = .register config.addressScratch)) = false := by
          intro xs hxs
          induction xs with
          | nil => rfl
          | cons move xs ihxs =>
              simp [hxs move (by simp),
                ihxs (fun other hother => hxs other (by simp [hother]))]
        apply hfalse
        intro move hmove
        have hmoveReserved := hreserved move hmove
        simp [hmoveReserved.1, hmoveReserved.2.1,
          hmoveReserved.2.2.1, hmoveReserved.2.2.2]
      have htailResult := ih htailDestinations htailNoSource htailReserved
      have htailAux :
          wordStackParallelLocationMoveAux config (tail.length + 1) tail =
            wordStackSequentialLocationMove (α := Nat) config tail := by
        simpa [wordStackParallelLocationMove] using htailResult
      simp [wordStackParallelLocationMove,
        wordStackParallelLocationMoveAux,
        wordStackLocationMoveDestinations, hdestinations', hany,
        hheadReady, hremoved, wordStackSequentialLocationMove,
        htailAux]

end Flapjack.RiscV
