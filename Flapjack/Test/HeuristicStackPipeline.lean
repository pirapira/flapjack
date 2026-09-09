import Flapjack.RiscV.HeuristicStackPipeline

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

end Flapjack.RiscV
