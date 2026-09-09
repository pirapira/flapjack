import Flapjack.RiscV.HeuristicStackPipeline
import Flapjack.RiscV.CorrectnessStackFunctionEntry

/-!
# Heuristic allocator-to-StackLang execution contract

The full-SSA heuristic graph allocator and the location-aware Word-to-Stack
lowering are packaged together by \`HeuristicStackPipeline\`.  This theorem
keeps the graph checks and exposes the same entry-moves/body execution
boundary used by the spill and linear-scan allocator contracts.
-/

namespace Flapjack.RiscV

open Flapjack

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
  exact ⟨hcontract.1, hcontract.2.1, hcontract.2.2.1, hbody, hmoves, hjoin,
    by simpa [hjoin] using heval⟩

end Flapjack.RiscV
