import Flapjack.RiscV.SpillCosts
import Flapjack.RiscV.AllocatorDriver
import Flapjack.RiscV.LinearScanDriver

/-!
# Heuristic and allocation-mode function driver

This is the executable composition corresponding to CakeML's allocator
decision boundary: an accepted oracle wins first, then the selected register
allocator is attempted, and finally the checked spill allocator is used.  The
older heuristic driver below is retained for compatibility; the mode-aware
entry point records linear-scan results explicitly instead of silently routing
them through the graph allocator.
-/

namespace Flapjack

inductive WordFunctionAllocationModeResult (α : Type) where
  | oracle (state : WordSsaState) (parameters : List Nat)
      (program : WordProg α)
  | graph (state : WordSsaState) (parameters : List Nat)
      (allocation : WordGraphAllocation) (program : WordProg α)
  | linearScan (state : WordSsaState) (parameters : List Nat)
      (allocation : WordLinearScanState) (program : WordProg α)
  | spill (state : WordSsaState) (parameters : List Nat)
      (allocation : WordSpillState) (program : WordProg α)
  deriving Repr

/-! The source `select_reg_alloc` chooses linear scan for modes `4` and
larger.  This driver keeps that choice visible in its result, while preserving
the oracle-first and spill-fallback behavior of the existing entry point. -/
def wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationModeResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else if 4 ≤ algorithm then
    match wordAllocateLinearScanFunctionWithEntry parameters program colours
        stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.linearScan state renamedParameters allocation renamedProgram)
    | none => none
  else
    match wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
        fixedSources algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

theorem wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry_linear_safe
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordLinearScanState)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry parameters
        program fixedSources algorithm currentFunction colours stackStart oracle =
        some (.linearScan state renamedParameters allocation renamedProgram)) :
    wordLinearScanAllocationSafe
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        (wordProgForcedClashes
          (wordSsaRenameFunctionWithEntry parameters program).2.snd)
        allocation = true := by
  simp [wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · split at halloc
    · cases hlinear : wordAllocateLinearScanFunctionWithEntry parameters
        program colours stackStart with
      | none => simp [hlinear] at halloc
      | some value =>
          cases value with
          | mk allocationState rest =>
              cases rest with
              | mk allocationParameters rest =>
                  cases rest with
                  | mk allocation' allocationProgram =>
                      simp [hlinear] at halloc
                      rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                      exact wordAllocateLinearScanFunctionWithEntry_safe
                        parameters program colours stackStart allocationState
                        allocationParameters allocation' allocationProgram hlinear
    · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
          parameters program fixedSources algorithm currentFunction colours
          stackStart with
      | none =>
          cases hspill :
              wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
                parameters program with
          | none => simp [hgraph, hspill] at halloc
          | some value => simp [hgraph, hspill] at halloc
      | some value => simp [hgraph] at halloc

theorem wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry_oracle_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry parameters
        program fixedSources algorithm currentFunction colours stackStart oracle =
        some (.oracle state renamedParameters renamedProgram)) :
    wordOracleColouringOk colours stackStart
      (WordClashTree.seq
        (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
      (wordProgForcedClashes
        (wordSsaRenameFunctionWithEntry parameters program).2.snd) oracle = true := by
  simp [wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry] at halloc
  split at halloc
  · assumption
  · split at halloc
    · cases hlinear : wordAllocateLinearScanFunctionWithEntry parameters
        program colours stackStart <;> simp [hlinear] at halloc
    · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters
        program fixedSources algorithm currentFunction colours stackStart with
      | some value => simp [hgraph] at halloc
      | none =>
          cases hspill :
              wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
                parameters program with
          | none => simp [hgraph, hspill] at halloc
          | some value => simp [hgraph, hspill] at halloc

theorem wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry parameters
        program fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · split at halloc
    · cases hlinear : wordAllocateLinearScanFunctionWithEntry parameters
        program colours stackStart <;> simp [hlinear] at halloc
    · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
        parameters program fixedSources algorithm currentFunction colours
        stackStart with
      | none =>
          cases hspill :
              wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
                parameters program with
          | none => simp [hgraph, hspill] at halloc
          | some value => simp [hgraph, hspill] at halloc
      | some value =>
          cases value with
          | mk graphState rest =>
              cases rest with
              | mk graphParameters rest =>
                  cases rest with
                  | mk graphAllocation graphProgram =>
                      simp [hgraph] at halloc
                      rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                      exact wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound
                        parameters program fixedSources algorithm currentFunction
                        colours stackStart graphState graphParameters
                        graphAllocation graphProgram hgraph

theorem wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry_spill_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordSpillState)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry parameters
        program fixedSources algorithm currentFunction colours stackStart oracle =
        some (.spill state renamedParameters allocation renamedProgram)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) := by
  simp [wordAllocateFunctionWithOracleOrAllocationModeOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · split at halloc
    · cases hlinear : wordAllocateLinearScanFunctionWithEntry parameters
        program colours stackStart <;> simp [hlinear] at halloc
    · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
        parameters program fixedSources algorithm currentFunction colours
        stackStart with
      | some value => simp [hgraph] at halloc
      | none =>
          cases hspill :
              wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
                parameters program with
          | none => simp [hgraph, hspill] at halloc
          | some value =>
              cases value with
              | mk spillState rest =>
                  cases rest with
                  | mk spillParameters rest =>
                      cases rest with
                      | mk spillProgram spillAllocation =>
                          simp [hgraph, hspill] at halloc
                          rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                          have hsound :=
                            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_sound
                              parameters program spillState spillParameters spillProgram
                              spillAllocation hspill
                          have hparameters :=
                            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_preserves_parameters
                              parameters program spillState spillParameters spillProgram
                              spillAllocation hspill
                          exact ⟨hsound.1, hsound.2.1, hsound.2.2,
                            hparameters⟩


def wordAllocateFunctionWithOracleOrHeuristicOrSpill
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunction parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else
    match wordAllocateGraphFunctionWithHeuristics parameters program fixedSources
        algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

def wordHeuristicDriverUsesOracle
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsOracle result

def wordHeuristicDriverUsesGraph
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsGraph result

def wordHeuristicDriverUsesSpill
    (result : Option (WordFunctionAllocationResult α)) : Bool :=
  wordFunctionAllocationResultIsSpill result

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpill_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpill parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpill] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithHeuristics parameters program
      fixedSources algorithm currentFunction colours stackStart with
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithClashTreeWithSpillsAndPreferences
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value => simp [hgraph, hspill] at halloc
    | some value =>
        cases value with
        | mk graphState rest =>
            cases rest with
            | mk graphParameters rest =>
                cases rest with
                | mk graphAllocation graphProgram =>
                    simp [hgraph] at halloc
                    rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                    exact wordAllocateGraphFunctionWithHeuristics_sound
                      parameters program fixedSources algorithm currentFunction
                      colours stackStart graphState graphParameters
                      graphAllocation graphProgram hgraph

/-! Full-SSA version of the heuristic decision boundary.  The entry moves
    are included in the oracle check, graph allocation, and spill fallback. -/
def wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) :
    Option (WordFunctionAllocationResult α) :=
  let (state, renamedParameters, renamedProgram) :=
    wordSsaRenameFunctionWithEntry parameters program
  let tree := WordClashTree.seq (.set renamedParameters)
    (wordClashTree renamedProgram [])
  let forced := wordProgForcedClashes renamedProgram
  let colour := wordOracleColour oracle
  if wordOracleColouringOk colours stackStart tree forced oracle then
    some (.oracle state renamedParameters
      (wordApplyColour colour renamedProgram))
  else
    match wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
        fixedSources algorithm currentFunction colours stackStart with
    | some (state, renamedParameters, allocation, renamedProgram) =>
        some (.graph state renamedParameters allocation renamedProgram)
    | none =>
        match wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
            parameters program with
        | none => none
        | some (state, renamedParameters, renamedProgram, allocation) =>
            some (.spill state renamedParameters allocation renamedProgram)

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_graph_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.graph state renamedParameters allocation renamedProgram)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck
        (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters
      program fixedSources algorithm currentFunction colours stackStart with
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value => simp [hgraph, hspill] at halloc
    | some value =>
        cases value with
        | mk graphState rest =>
            cases rest with
            | mk graphParameters rest =>
                cases rest with
                | mk graphAllocation graphProgram =>
                    simp [hgraph] at halloc
                    rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                    exact wordAllocateGraphFunctionWithHeuristicsEntryRenamed_sound
                      parameters program fixedSources algorithm currentFunction
                      colours stackStart graphState graphParameters
                      graphAllocation graphProgram hgraph

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_oracle_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.oracle state renamedParameters renamedProgram)) :
    wordOracleColouringOk colours stackStart
      (WordClashTree.seq
        (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
      (wordProgForcedClashes
        (wordSsaRenameFunctionWithEntry parameters program).2.snd) oracle = true := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry] at halloc
  split at halloc
  · assumption
  · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters
      program fixedSources algorithm currentFunction colours stackStart with
    | some value => simp [hgraph] at halloc
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value => simp [hgraph, hspill] at halloc

theorem wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry_spill_sound
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (oracle : NatInfoMap Nat) (state : WordSsaState)
    (renamedParameters : List Nat) (allocation : WordSpillState)
    (renamedProgram : WordProg α)
    (halloc :
      wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry parameters program
        fixedSources algorithm currentFunction colours stackStart oracle =
        some (.spill state renamedParameters allocation renamedProgram)) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) := by
  simp [wordAllocateFunctionWithOracleOrHeuristicOrSpillEntry] at halloc
  split at halloc
  · simp_all
  · cases hgraph : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters
      program fixedSources algorithm currentFunction colours stackStart with
    | some value => simp [hgraph] at halloc
    | none =>
        cases hspill :
            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
              parameters program with
        | none => simp [hgraph, hspill] at halloc
        | some value =>
            cases value with
            | mk spillState rest =>
                cases rest with
                | mk spillParameters rest =>
                    cases rest with
                    | mk spillProgram spillAllocation =>
                        simp [hgraph, hspill] at halloc
                        rcases halloc with ⟨rfl, rfl, rfl, rfl⟩
                        have hsound :=
                          wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_sound
                            parameters program spillState spillParameters spillProgram
                            spillAllocation hspill
                        have hparameters :=
                          wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed_preserves_parameters
                            parameters program spillState spillParameters spillProgram
                            spillAllocation hspill
                        exact ⟨hsound.1, hsound.2.1, hsound.2.2, hparameters⟩

end Flapjack
