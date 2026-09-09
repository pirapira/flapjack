import Flapjack.RiscV.HeuristicPipeline

/-! Regression coverage for the heuristic-allocated RISC-V pipeline. -/

namespace Flapjack

def heuristicTargetRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def heuristicTargetDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

example :
    pipelineWordFunctionsAllocatedWithHeuristics 1
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithHeuristics 1
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

#guard
    (pipelineWordFunctionsAllocatedWithHeuristics 1
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome = true

#guard
    (compileFlapjackRiscVViaHeuristicAllocatedStackTarget 1 .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      heuristicTargetRemoveConfig heuristicTargetDeclarations).isSome

end Flapjack
