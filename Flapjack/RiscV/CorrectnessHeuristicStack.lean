import Flapjack.RiscV.HeuristicStackPipeline
import Flapjack.RiscV.CorrectnessStackFunctionEntry
import Flapjack.RiscV.CorrectnessGraphLocations
import Flapjack.RiscV.CorrectnessGraphCoverage
import Flapjack.RiscV.OracleAllocator
import Flapjack.RiscV.AllocatorCorrectness

/-!
# Heuristic allocator-to-StackLang execution contract

The full-SSA heuristic graph allocator and the location-aware Word-to-Stack
lowering are packaged together by \`HeuristicStackPipeline\`.  This theorem
keeps the graph checks and exposes the same entry-moves/body execution
boundary used by the spill and linear-scan allocator contracts.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordAllocateGraphForHeuristics_bijection
    (algorithm : Nat) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fixedSources : List Nat)
    (moves colourMoves : List WordMove) (colours stackStart : Nat)
    (spillCosts : Option (NatInfoMap Nat)) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraphForHeuristics algorithm tree forced fixedSources
      moves colourMoves colours stackStart spillCosts = some allocation) :
    allocation.bijection = (wordInitRegAlloc tree forced fixedSources).bijection := by
  by_cases hsimple : algorithm < 2
  · cases spillCosts with
    | none =>
        have hgraph : wordAllocateGraphSimpleWithColourMoves tree forced
            fixedSources colourMoves colours stackStart = some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        simp [wordAllocateGraphSimpleWithColourMoves] at hgraph
        rcases hgraph with ⟨_, heq⟩
        cases heq
        rfl
    | some costs =>
        have hgraph : wordAllocateGraphSimpleWithColourMovesAndSpillCosts tree
            forced fixedSources colourMoves colours stackStart costs =
            some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        simp [wordAllocateGraphSimpleWithColourMovesAndSpillCosts] at hgraph
        rcases hgraph with ⟨_, heq⟩
        cases heq
        rfl
  · cases spillCosts with
    | none =>
        have hgraph : wordAllocateGraphWithPrefreezeMoves tree forced
            fixedSources moves colourMoves colours stackStart = some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        simp [wordAllocateGraphWithPrefreezeMoves, wordGraphCheckAllocation,
          wordAllocateGraphWithPrefreezeMovesCandidate] at hgraph
        rcases hgraph with ⟨_, heq⟩
        cases heq
        rfl
    | some costs =>
        have hgraph : wordAllocateGraphWithPrefreezeMovesAndSpillCosts tree forced
            fixedSources moves colourMoves colours stackStart costs =
            some allocation := by
          simpa [wordAllocateGraphForHeuristics, hsimple] using halloc
        simp [wordAllocateGraphWithPrefreezeMovesAndSpillCosts,
          wordGraphCheckAllocation,
          wordAllocateGraphWithPrefreezeMovesAndSpillCostsCandidate] at hgraph
        rcases hgraph with ⟨_, heq⟩
        cases heq
        rfl

theorem wordAllocateGraphFunctionWithHeuristicsEntryRenamed_maps_parameters
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithHeuristicsEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation'
  have hgraphFull :
      wordAllocateGraphForHeuristics algorithm
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))
        (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources
          (wordStackOnly renamedProgram).forced)
        (wordGetHeuristics algorithm currentFunction renamedProgram).1
        (wordProgPrioritizedMoves renamedProgram) colours stackStart
        (wordGetHeuristics algorithm currentFunction renamedProgram).2 =
        some allocation := by
    simpa [hstate, hparameters, hprogram] using hgraph
  have hbij := wordAllocateGraphForHeuristics_bijection algorithm
    ((WordClashTree.set renamedParameters).seq
      (wordClashTree renamedProgram []))
    (wordProgForcedClashes renamedProgram)
    (wordStackOnlyUnion fixedSources
      (wordStackOnly renamedProgram).forced)
    (wordGetHeuristics algorithm currentFunction renamedProgram).1
    (wordProgPrioritizedMoves renamedProgram) colours stackStart
    (wordGetHeuristics algorithm currentFunction renamedProgram).2
    allocation hgraphFull
  intro name hname
  have hname' :
      name ∈ (wordSsaRenameFunctionWithEntry parameters program).2.fst := by
    simpa [hparameters] using hname
  have hnode := wordListRemap_lookup_of_mem
    (wordSsaRenameFunctionWithEntry parameters program).2.fst
      (wordClashTreeBijection
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
      { toNode := [], fromNode := [], next := 0 }) name hname'
  simpa [hstate, hparameters, hprogram, hbij, wordInitRegAlloc,
    wordMkBijection, wordClashTreeBijection] using hnode

theorem wordAllocateGraphFunctionWithHeuristicsEntryRenamed_maps_locations
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ wordClashTreeNames
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram [])) →
      ∃ location,
        lookupNatInfo name (wordGraphLocations allocation colours stackStart) =
          some location := by
  simp [wordAllocateGraphFunctionWithHeuristicsEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, hstate, hparameters,
    hallocation, hprogram⟩
  subst allocation'
  have hgraphFull :
      wordAllocateGraphForHeuristics algorithm
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))
        (wordProgForcedClashes renamedProgram)
        (wordStackOnlyUnion fixedSources
          (wordStackOnly renamedProgram).forced)
        (wordGetHeuristics algorithm currentFunction renamedProgram).1
        (wordProgPrioritizedMoves renamedProgram) colours stackStart
        (wordGetHeuristics algorithm currentFunction renamedProgram).2 =
        some allocation := by
    simpa [hstate, hparameters, hprogram] using hgraph
  have hbij := wordAllocateGraphForHeuristics_bijection algorithm
    ((WordClashTree.set renamedParameters).seq
      (wordClashTree renamedProgram []))
    (wordProgForcedClashes renamedProgram)
    (wordStackOnlyUnion fixedSources
      (wordStackOnly renamedProgram).forced)
    (wordGetHeuristics algorithm currentFunction renamedProgram).1
    (wordProgPrioritizedMoves renamedProgram) colours stackStart
    (wordGetHeuristics algorithm currentFunction renamedProgram).2
    allocation hgraphFull
  intro name hname
  have hnode := wordClashTreeBijection_maps_names
    ((WordClashTree.set renamedParameters).seq
      (wordClashTree renamedProgram []))
    { toNode := [], fromNode := [], next := 0 } name hname
  rcases hnode with ⟨node, hnode⟩
  have hnode' : lookupNatInfo name
      (wordMkBijection
        ((WordClashTree.set renamedParameters).seq
          (wordClashTree renamedProgram []))).toNode = some node := by
    simpa [wordMkBijection] using hnode
  have hinverse := wordMkBijection_lookup_inverse
    ((WordClashTree.set renamedParameters).seq
      (wordClashTree renamedProgram [])) name node hnode'
  apply wordGraphLocations_lookup_of_fromNode
  simpa [hstate, hparameters, hprogram, hbij, wordInitRegAlloc,
    wordMkBijection, wordClashTreeBijection] using hinverse

theorem evalWordStackMachine_wordAllocateGraphFunctionWithHeuristicsEntryToStack
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (renamedProgram : WordProg (Word width)) (stackProgram : StackProg Nat)
    (finalState : WordStackBitmapState)
    (body moves : StackProg Nat)
    (machineState middle final : WordStackMachineState width)
    (bodyState : WordStackBitmapState)
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart =
      some (ssaState, renamedParameters, allocation, renamedProgram))
    (hbridge : wordAllocateGraphFunctionWithHeuristicsEntryToStack config
      parameters program fixedSources algorithm currentFunction colours stackStart
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram, finalState))
    (hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := wordGraphLocations allocation colours stackStart }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState
      renamedProgram = some (body, bodyState))
    (hmoves : wordStackMovesFromPhysical
      { config with locations := wordGraphLocations allocation colours stackStart }
      renamedParameters 2 = some moves)
    (hentry : evalWordStackMachine machineState moves = some middle)
    (hbodyEval : evalWordStackMachine middle body = some final) :
    wordGraphTagsAreFixed allocation.graph = true ∧
    wordGraphColouringRespectsEdges allocation.graph = true ∧
      (wordClashTreeCheck (wordGraphColouringAt allocation.colouring)
        (WordClashTree.seq
          (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
        [] []).isSome = true ∧
      (∀ name, name ∈ renamedParameters →
        ∃ node, lookupNatInfo name allocation.bijection.toNode = some node) ∧
      wordToStackProgWordWithLocationBitmaps
        { config with locations := wordGraphLocations allocation colours stackStart }
        registerCount bitmapRegister frameSlots storeConstsStub bitmapState
        renamedProgram = some (body, bodyState) ∧
      wordStackMovesFromPhysical
        { config with locations := wordGraphLocations allocation colours stackStart }
        renamedParameters 2 = some moves ∧
      stackProgram = wordStackJoin moves body ∧
      evalWordStackMachine machineState stackProgram = some final := by
  have hcontract := wordAllocateGraphFunctionWithHeuristicsEntryToStack_contract
    config parameters program fixedSources algorithm currentFunction colours stackStart
    registerCount bitmapRegister frameSlots storeConstsStub bitmapState
    ssaState renamedParameters allocation renamedProgram stackProgram finalState
    halloc hbridge
  have hstack := wordAllocateGraphFunctionWithHeuristicsEntryToStack_stack_result
    config parameters program fixedSources algorithm currentFunction colours stackStart
    registerCount bitmapRegister frameSlots storeConstsStub bitmapState
    ssaState renamedParameters allocation renamedProgram stackProgram finalState hbridge
  simp only [wordToStackFunctionWithGraphAllocationAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps] at hstack
  simp [hbody, hmoves] at hstack
  have hjoin : stackProgram = wordStackJoin moves body := by
    exact hstack.1.symm
  have heval := evalWordStackMachine_wordStackJoin machineState middle final
    moves body hentry hbodyEval
  have hparameters :=
    wordAllocateGraphFunctionWithHeuristicsEntryRenamed_maps_parameters
      parameters program fixedSources algorithm currentFunction colours stackStart
      ssaState renamedParameters allocation renamedProgram halloc
  exact ⟨hcontract.1, hcontract.2.1, hcontract.2.2.1, hparameters, hbody,
    hmoves, hjoin, by simpa [hjoin] using heval⟩

end Flapjack.RiscV
