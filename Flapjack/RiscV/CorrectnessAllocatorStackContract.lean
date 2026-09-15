import Flapjack.RiscV.CorrectnessAllocatorStackDecomposition

/-!
# Combined allocator-to-StackLang contract

This is the public correctness boundary for the full-SSA spill allocator.
It keeps the allocator witness, the body/entry-move decomposition, and the
StackLang execution result together so later RISC-V proofs can consume the
whole package without unfolding its executable implementation.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordAllocateSsaFunctionWithEntryAndSpillToStack_contract
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg (Word width)) (allocation : WordSpillState)
    (stackProgram : StackProg Nat) (finalState : WordStackBitmapState)
    (body : StackProg Nat)
    (machineState final : WordStackMachineState width)
    (bodyState : WordStackBitmapState)
    (hbridge : wordAllocateSsaFunctionWithEntryAndSpillToStack config parameters
      program registerCount bitmapRegister frameSlots storeConstsStub bitmapState =
      some (ssaState, renamedParameters, renamedProgram, allocation,
        stackProgram, finalState))
    (hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState
      renamedProgram = some (body, bodyState))
    (hbodyEval : evalWordStackMachine machineState body = some final) :
    wordSpillAllocationRespectsClashes
        (wordClashTreeAnalyze
          (wordClashTree
            (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
          []).snd allocation.locations = true ∧
      wordProgSpecialLocationsSafe allocation.locations
        (wordSsaRenameFunctionWithEntry parameters program).2.snd = true ∧
      wordSpillClashTreeChecked
        (wordClashTree
          (wordSsaRenameFunctionWithEntry parameters program).2.snd [])
        allocation.locations = true ∧
      (∀ name, name ∈ wordProgVariables renamedProgram →
        ∃ location, lookupNatInfo name allocation.locations = some location) ∧
      (∀ name, name ∈ parameters →
        lookupNatInfo name allocation.locations = some (.register name)) ∧
      wordToStackProgWordWithLocationBitmaps
        { config with locations := allocation.locations }
        registerCount bitmapRegister frameSlots storeConstsStub bitmapState
        renamedProgram = some (body, bodyState) ∧
      stackProgram = body ∧
      bodyState = finalState ∧
      evalWordStackMachine machineState stackProgram = some final := by
  have hwitness := wordAllocateSsaFunctionWithEntryAndSpillToStack_witness
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState hbridge
  have hstack := wordAllocateSsaFunctionWithEntryAndSpillToStack_stack_result
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState hbridge
  simp only [wordToStackFunctionWithSpillStateAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps] at hstack
  simp [hbody] at hstack
  have hjoin : stackProgram = body := by
    exact hstack.1.symm
  have hstate : bodyState = finalState := by
    exact hstack.2
  have heval := evalWordStackMachine_wordAllocateSsaFunctionWithEntryAndSpillToStack
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState body machineState final bodyState hbridge hbody hbodyEval
  exact ⟨hwitness.1, hwitness.2.1, hwitness.2.2.1, hwitness.2.2.2.1,
    hwitness.2.2.2.2, hbody, hjoin, hstate, heval⟩

end Flapjack.RiscV
