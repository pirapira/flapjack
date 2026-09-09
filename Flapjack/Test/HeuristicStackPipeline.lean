import Flapjack.RiscV.CorrectnessHeuristicStack

/-! Regression coverage for the full-SSA heuristic graph-to-Stack bridge. -/

namespace Flapjack.RiscV

open Flapjack

def heuristicStackTestConfig : WordStackConfig :=
  { locations := [], scratch := 31, stackBase := 0, addressScratch := 29 }

def heuristicStackTestBitmapState : WordStackBitmapState :=
  { data := [], length := 0 }

#guard
  (wordAllocateGraphFunctionWithHeuristicsEntryToStack
    heuristicStackTestConfig [] (.skip : WordProg (Word 64)) [] 1 0 2 0
    0 0 0 none heuristicStackTestBitmapState).isSome

example [NeZero width]
    (hresult : wordAllocateGraphFunctionWithHeuristicsEntryToStack
      heuristicStackTestConfig [] (.skip : WordProg (Word width)) [] 1 0 2 0
      0 0 0 none heuristicStackTestBitmapState =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram, finalState)) :
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps
      heuristicStackTestConfig renamedParameters allocation 2 0 0 0 0 none
      heuristicStackTestBitmapState renamedProgram =
      some (stackProgram, finalState) := by
  exact wordAllocateGraphFunctionWithHeuristicsEntryToStack_stack_result
    heuristicStackTestConfig [] (.skip : WordProg (Word width)) [] 1 0 2 0
    0 0 0 none heuristicStackTestBitmapState ssaState renamedParameters allocation
    renamedProgram stackProgram finalState hresult

example [NeZero width]
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
      [] (.skip : WordProg (Word width)) [] 1 0 2 0 =
      some (ssaState, renamedParameters, allocation, renamedProgram))
    (hbridge : wordAllocateGraphFunctionWithHeuristicsEntryToStack
      heuristicStackTestConfig [] (.skip : WordProg (Word width)) [] 1 0 2 0
      0 0 0 none heuristicStackTestBitmapState =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram, finalState)) :
    wordGraphTagsAreFixed allocation.graph = true ∧
      wordGraphColouringRespectsEdges allocation.graph = true := by
  have hcontract := wordAllocateGraphFunctionWithHeuristicsEntryToStack_contract
    heuristicStackTestConfig [] (.skip : WordProg (Word width)) [] 1 0 2 0
    0 0 0 none heuristicStackTestBitmapState ssaState renamedParameters allocation
    renamedProgram stackProgram finalState halloc hbridge
  exact ⟨hcontract.1, hcontract.2.1⟩

example [NeZero width]
    (halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
      [] (.skip : WordProg (Word width)) [] 1 0 2 0 =
      some (ssaState, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  exact wordAllocateGraphFunctionWithHeuristicsEntryRenamed_maps_parameters
    [] (.skip : WordProg (Word width)) [] 1 0 2 0
    ssaState renamedParameters allocation renamedProgram halloc

end Flapjack.RiscV
