import Flapjack.RiscV.CorrectnessStackParallelMoveAcyclic

/-!
# Evaluating source-ordered StackLang moves

The acyclic scheduler equation reduces parallel moves to a sequence of
location moves.  This file starts the evaluator side of that contract by
exposing the intermediate machine state hidden by `wordStackJoin`.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_wordStackJoin_exists [NeZero width]
    (state final : WordStackMachineState width)
    (first second : StackProg Nat)
    (heval : evalWordStackMachine state (wordStackJoin first second) = some final) :
    ∃ middle,
      evalWordStackMachine state first = some middle ∧
        evalWordStackMachine middle second = some final := by
  by_cases hfirstSkip : first = .skip
  · subst first
    exact ⟨state, by simp [evalWordStackMachine], heval⟩
  by_cases hsecondSkip : second = .skip
  · subst second
    have hfirst : evalWordStackMachine state first = some final := by
      simpa [wordStackJoin] using heval
    exact ⟨final, hfirst, by simp [evalWordStackMachine]⟩
  · rw [wordStackJoin_eq_seq_of_ne_skip first second hfirstSkip hsecondSkip]
      at heval
    simp only [evalWordStackMachine] at heval
    cases hfirst : evalWordStackMachine state first with
    | none => simp [hfirst] at heval
    | some middle =>
        refine ⟨middle, rfl, ?_⟩
        simpa [hfirst] using heval

theorem evalWordStackMachine_sequentialLocationMove_preserves_other_value
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (moves : List (WordLocation × WordLocation)) (other : WordLocation)
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch)
    (hotherDestination : other ∉ moves.map Prod.fst)
    (hotherScratch : other ≠ .register config.scratch)
    (heval : (wordStackSequentialLocationMove (α := Nat) config moves).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final other =
      wordStackLocationValue config state other := by
  induction moves generalizing state final with
  | nil =>
      simp [wordStackSequentialLocationMove] at heval
      cases heval
      rfl
  | cons head tail ih =>
      have hdestinations' :
          (head.1 :: tail.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hdestinations
      have htailDestinations : (tail.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hdestinations').2
      have htailReserved : ∀ move, move ∈ tail →
          move.1 ≠ .register config.scratch ∧
          move.1 ≠ .register config.addressScratch ∧
          move.2 ≠ .register config.scratch ∧
          move.2 ≠ .register config.addressScratch := by
        intro move hmove
        exact hreserved move (by simp [hmove])
      have hheadReserved := hreserved head (by simp)
      have hotherHead : other ≠ head.1 := by
        intro heq
        apply hotherDestination
        simp [heq]
      have hotherTail : other ∉ tail.map Prod.fst := by
        intro hmove
        apply hotherDestination
        simp [hmove]
      have hheadMove :
          wordStackLocationMove (α := Nat) config head.1 head.2 ≠ none := by
        cases head.1 <;> cases head.2 <;>
          simp [wordStackLocationMove] <;> split <;> simp
      have hheadMove' : ∃ first,
          wordStackLocationMove (α := Nat) config head.1 head.2 = some first := by
        cases hmove : wordStackLocationMove (α := Nat) config head.1 head.2 with
        | none => exact False.elim (hheadMove hmove)
        | some first => exact ⟨first, rfl⟩
      obtain ⟨first, hfirst⟩ := hheadMove'
      rw [wordStackSequentialLocationMove, hfirst] at heval
      cases htail : wordStackSequentialLocationMove (α := Nat) config tail with
      | none => simp [htail] at heval
      | some rest =>
          simp [htail] at heval
          obtain ⟨middle, hfirstEval, hrestEval⟩ :=
            evalWordStackMachine_wordStackJoin_exists state final first rest heval
          have hfirstEval' :
              (wordStackLocationMove (α := Nat) config head.1 head.2).bind
                (evalWordStackMachine state) = some middle := by
            simpa [hfirst] using hfirstEval
          have hfirstOther :=
            evalWordStackMachine_locationMove_preserves_other_value
              config state middle head.1 head.2 other hotherHead hotherScratch
              hfirstEval'
          have htailEval :
              (wordStackSequentialLocationMove (α := Nat) config tail).bind
                (evalWordStackMachine middle) = some final := by
            rw [htail]
            simpa using hrestEval
          have htailOther := ih middle final htailDestinations htailReserved
            hotherTail htailEval
          calc
            wordStackLocationValue config final other =
                wordStackLocationValue config middle other := htailOther
            _ = wordStackLocationValue config state other := hfirstOther

theorem evalWordStackMachine_parallelLocationMove_acyclic_preserves_other_value
    [NeZero width]
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
  rw [wordStackParallelLocationMove_acyclic_eq_sequential config moves
    hdestinations hnoSource hreserved] at heval
  exact evalWordStackMachine_sequentialLocationMove_preserves_other_value
    config state final moves other hdestinations hreserved hotherDestination
    hotherScratch heval

end Flapjack.RiscV
