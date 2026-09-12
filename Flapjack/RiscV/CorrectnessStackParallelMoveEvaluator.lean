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

theorem evalWordStackMachine_sequentialLocationMove_preserves_move_value
    [NeZero width]
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
    (heval : (wordStackSequentialLocationMove (α := Nat) config moves).bind
      (evalWordStackMachine state) = some final) :
    wordStackLocationValue config final target.1 =
      wordStackLocationValue config state target.2 := by
  induction moves generalizing state final with
  | nil => simp at htarget
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
      have hheadReserved := hreserved head (by simp)
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
          have htailEval :
              (wordStackSequentialLocationMove (α := Nat) config tail).bind
                (evalWordStackMachine middle) = some final := by
            rw [htail]
            simpa using hrestEval
          have htarget' : target = head ∨ target ∈ tail := by
            simpa using htarget
          rcases htarget' with hhead | htarget
          ·
            subst target
            have hheadValue :=
              evalWordStackMachine_locationMove_preserves_value
                config state middle head.1 head.2 hfirstEval'
            have hheadNotTailDestination : head.1 ∉ tail.map Prod.fst := by
              intro hmove
              exact (List.nodup_cons.mp hdestinations').1 hmove
            have htailValue :=
              evalWordStackMachine_sequentialLocationMove_preserves_other_value
                config middle final tail head.1 htailDestinations htailReserved
                hheadNotTailDestination hheadReserved.1 htailEval
            calc
              wordStackLocationValue config final head.1 =
                  wordStackLocationValue config middle head.1 := htailValue
              _ = wordStackLocationValue config state head.2 := hheadValue
          · have htargetTail : target ∈ tail := htarget
            have htargetSourceNoDest : target.2 ∉ head.1 :: tail.map Prod.fst :=
              hnoSource target (by simp [htargetTail])
            have htargetSourceNotHead : target.2 ≠ head.1 := by
              intro heq
              apply htargetSourceNoDest
              simp [heq]
            have htargetSourceScratch := hreserved target (by simp [htargetTail])
            have hfirstSource :=
              evalWordStackMachine_locationMove_preserves_other_value
                config state middle head.1 head.2 target.2
                htargetSourceNotHead htargetSourceScratch.2.2.1 hfirstEval'
            have htailValue := ih middle final htailDestinations htailNoSource
              htailReserved htargetTail htailEval
            calc
              wordStackLocationValue config final target.1 =
                  wordStackLocationValue config middle target.2 := htailValue
              _ = wordStackLocationValue config state target.2 := hfirstSource

theorem evalWordStackMachine_parallelLocationMove_acyclic_preserves_move_value
    [NeZero width]
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
  rw [wordStackParallelLocationMove_acyclic_eq_sequential config moves
    hdestinations hnoSource hreserved] at heval
  exact evalWordStackMachine_sequentialLocationMove_preserves_move_value
    config state final moves target hdestinations hnoSource hreserved htarget heval

/-! The location-level frame theorem lifts directly to the allocator's
    variable-to-location relation.  This is the useful boundary for function
    entry: parameter destinations may be overwritten, while every unrelated
    mapped variable keeps its value through the physical move prefix. -/
theorem evalWordStackMachine_parallelLocationMove_acyclic_preserves_mapped_values_outside
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (moves : List (WordLocation × WordLocation))
    (values : Nat → Option (Word width))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch)
    (hvalues : wordStackMappedValues config values state)
    (houtside : ∀ name value location,
      values name = some value →
      wordStackLocation config name = some location →
      location ∉ moves.map Prod.fst)
    (hnotScratch : ∀ name value location,
      values name = some value →
      wordStackLocation config name = some location →
      location ≠ .register config.scratch)
    (heval : (wordStackParallelLocationMove config moves).bind
      (evalWordStackMachine state) = some final) :
    wordStackMappedValues config values final := by
  rw [wordStackParallelLocationMove_acyclic_eq_sequential config moves
    hdestinations hnoSource hreserved] at heval
  intro name value location hvalue hlocation
  change lookupNatInfo name config.locations = some location at hlocation
  have hstateValue := hvalues name value location hvalue hlocation
  have hstateLocationValue :
      wordStackLocationValue config state location = value := by
    cases location with
    | register register =>
        simpa [wordStackMachineValue, wordStackLocation,
          wordStackLocationValue, hlocation] using hstateValue
    | stack slot =>
        simpa [wordStackMachineValue, wordStackLocation,
          wordStackLocationValue, hlocation] using hstateValue
  have hpreserved :=
    evalWordStackMachine_sequentialLocationMove_preserves_other_value
      config state final moves location hdestinations hreserved
      (houtside name value location hvalue hlocation)
      (hnotScratch name value location hvalue hlocation) heval
  have hfinalLocationValue :
      wordStackLocationValue config final location = value := by
    rw [hpreserved]
    exact hstateLocationValue
  cases location with
  | register register =>
      simpa [wordStackMachineValue, wordStackLocation,
        wordStackLocationValue, hlocation] using hfinalLocationValue
  | stack slot =>
      simpa [wordStackMachineValue, wordStackLocation,
        wordStackLocationValue, hlocation] using hfinalLocationValue

theorem wordStackPhysicalMovesFromSpec_mem_source
    (locations : List WordLocation) (source : Nat)
    (move : WordLocation × WordLocation)
    (hmove : move ∈ wordStackPhysicalMovesFromSpec locations source) :
    ∃ index, move.2 = .register (source + 2 * index) := by
  induction locations generalizing source with
  | nil => simp [wordStackPhysicalMovesFromSpec] at hmove
  | cons location locations ih =>
      simp only [wordStackPhysicalMovesFromSpec, List.mem_cons] at hmove
      rcases hmove with rfl | hmove
      · exact ⟨0, by simp⟩
      · obtain ⟨index, hindex⟩ := ih (source := source + 2) hmove
        refine ⟨index + 1, ?_⟩
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hindex

/-! Physical parameter moves retain the source-register shape introduced by
    the ABI lowering.  This is the list-level bridge needed by callers that
    reason about all generated entry moves at once, rather than a selected
    location move. -/
theorem evalWordStackMachine_movesFromPhysical_preserves_source_shape
    [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (destinations : List Nat) (source : Nat) (locations : List WordLocation)
    (moves : List (WordLocation × WordLocation))
    (hdestinations : (moves.map Prod.fst).Nodup)
    (hnoSource : ∀ move, move ∈ moves →
      move.2 ∉ moves.map Prod.fst)
    (hreserved : ∀ move, move ∈ moves →
      move.1 ≠ .register config.scratch ∧
      move.1 ≠ .register config.addressScratch ∧
      move.2 ≠ .register config.scratch ∧
      move.2 ≠ .register config.addressScratch)
    (hlookup : destinations.mapM (wordStackLocation config) = some locations)
    (hphysical : wordStackPhysicalMovesFrom config destinations source = some moves)
    (heval : (wordStackParallelLocationMove config moves).bind
      (evalWordStackMachine state) = some final) :
    ∀ move, move ∈ moves →
      ∃ index,
        move.2 = .register (source + 2 * index) ∧
        wordStackLocationValue config final move.1 =
          wordStackLocationValue config state move.2 := by
  have hspec := wordStackPhysicalMovesFrom_eq_spec config destinations source
    locations hlookup
  have hmoveSpec : moves = wordStackPhysicalMovesFromSpec locations source := by
    exact (Option.some.inj (hspec.symm.trans hphysical)).symm
  intro move hmove
  have hmoveSpec' : move ∈ wordStackPhysicalMovesFromSpec locations source := by
    simpa [hmoveSpec] using hmove
  obtain ⟨index, hsource⟩ := wordStackPhysicalMovesFromSpec_mem_source
    locations source move hmoveSpec'
  refine ⟨index, hsource, ?_⟩
  exact evalWordStackMachine_parallelLocationMove_acyclic_preserves_move_value
    config state final moves move hdestinations hnoSource hreserved hmove heval

end Flapjack.RiscV
