import Flapjack.RiscV.AllocationModePipeline

/-! Regression coverage for CakeML numeric allocation-mode dispatch. -/

namespace Flapjack

def allocationModeTargetRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def allocationModeTargetDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

example : wordAllocationAlgorithmOfNat 0 = .simple := by
  decide

example : wordAllocationAlgorithmOfNat 3 = .ircHeuristic := by
  decide

example : wordAllocationAlgorithmOfNat 19 = .linearScan := by
  decide

example :
    wordAllocationAlgorithmUsesHeuristics
      (wordAllocationAlgorithmOfNat 3) = true := by
  decide

example :
    wordAllocationAlgorithmIsLinearScanNat 4 = true := by
  decide

example :
    pipelineWordFunctionsAllocatedWithSourceAlgorithm 4
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithSourceAlgorithm 2
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

#guard
    (compileFlapjackRiscVViaSourceAlgorithmStackTarget 2 .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      allocationModeTargetRemoveConfig allocationModeTargetDeclarations).isSome

end Flapjack
