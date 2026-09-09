import Flapjack.RiscV.CorrectnessLinearScanStack

/-! Regression coverage for function-level linear-scan pipeline integration. -/

namespace Flapjack

def linearScanTargetRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def linearScanTargetDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

example :
    (wordAllocateLinearScanFunction [] (.skip : WordProg Nat) 2 0).isSome =
      true := by
  decide +kernel

example :
    (wordAllocateLinearScanFunctionWithEntry [] (.skip : WordProg Nat) 2 0).isSome =
      true := by
  decide +kernel

example :
    pipelineWordFunctionsAllocatedWithLinearScan
        ([] : List (Nat × List Nat × LoopProg (RiscV.Word 64))) =
      some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithLinearScan
      [(0, [], (.skip : LoopProg (RiscV.Word 64))) ]).isSome = true := by
  decide +kernel

#guard
    (compileFlapjackRiscVViaLinearScanStackTarget .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      linearScanTargetRemoveConfig linearScanTargetDeclarations).isSome

example
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunction parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  exact wordAllocateLinearScanFunction_maps_parameters
    parameters program colours stackStart state renamedParameters allocation
    renamedProgram halloc

example
    (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState) (renamedProgram : WordProg α)
    (halloc : wordAllocateLinearScanFunctionWithEntry parameters program colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ renamedParameters →
      ∃ location, lookupNatInfo name allocation.locations = some location := by
  exact wordAllocateLinearScanFunctionWithEntry_maps_parameters
    parameters program colours stackStart state renamedParameters allocation
    renamedProgram halloc

example [NeZero width]
    (config : RiscV.WordStackConfig) (parameters : List Nat)
    (program : WordProg (RiscV.Word width)) (colours stackStart : Nat)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordLinearScanState)
    (renamedProgram : WordProg (RiscV.Word width)) (stackProgram : StackProg Nat)
    (hbridge : RiscV.wordAllocateLinearScanFunctionWithEntryToStack config
      parameters program colours stackStart =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram)) :
    RiscV.wordToStackFunctionWithParameters
      { config with locations := wordLinearScanLocations allocation }
      renamedParameters renamedProgram = some stackProgram := by
  exact RiscV.wordAllocateLinearScanFunctionWithEntryToStack_stack_result
    config parameters program colours stackStart ssaState renamedParameters
    allocation renamedProgram stackProgram hbridge

end Flapjack
