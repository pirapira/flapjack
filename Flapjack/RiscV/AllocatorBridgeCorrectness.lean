import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.AllocatorCorrectness

/-!
Contracts for the public full-SSA spill allocator bridge.

`wordAllocateSsaFunctionWithEntryAndSpillToStack` packages allocation and
Word-to-Stack lowering in one executable result.  This file exposes the
allocator facts that remain available after that package boundary, so later
StackRemove and RISC-V proofs do not need to unfold the allocator again.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordAllocateSsaFunctionWithEntryAndSpillToStack_witness
    [NeZero width] (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg (Word width)) (allocation : WordSpillState)
    (stackProgram : StackProg Nat) (finalState : WordStackBitmapState)
    (hbridge : wordAllocateSsaFunctionWithEntryAndSpillToStack config parameters
      program registerCount bitmapRegister frameSlots storeConstsStub state =
      some (ssaState, renamedParameters, renamedProgram, allocation,
        stackProgram, finalState)) :
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
        lookupNatInfo name allocation.locations = some (.register name)) := by
  simp only [wordAllocateSsaFunctionWithEntryAndSpillToStack] at hbridge
  cases halloc :
      wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed
        parameters program with
  | none => simp [halloc] at hbridge
  | some allocationResult =>
      cases allocationResult with
      | mk allocationState allocationRest =>
          cases allocationRest with
          | mk allocationParameters allocationRest =>
              cases allocationRest with
              | mk allocationProgram allocation' =>
                  cases hstack :
                      wordToStackFunctionWithSpillStateAndLocationBitmaps config
                        allocationParameters allocation' registerCount bitmapRegister
                        frameSlots storeConstsStub state allocationProgram with
                  | none => simp [halloc, hstack] at hbridge
                  | some stackResult =>
                      cases stackResult with
                      | mk generatedProgram generatedState =>
                          have hresult :
                                allocationState = ssaState ∧
                                allocationParameters = renamedParameters ∧
                                allocationProgram = renamedProgram ∧
                                allocation' = allocation ∧
                                generatedProgram = stackProgram ∧
                                generatedState = finalState := by
                            simpa [halloc, hstack] using hbridge
                          rcases hresult with
                            ⟨rfl, rfl, rfl, hallocEq, rfl, rfl⟩
                          have hwitness :=
                            wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences_witness
                              parameters program allocationState allocationParameters
                              allocationProgram allocation' halloc
                          simpa [hallocEq] using hwitness

end Flapjack.RiscV
