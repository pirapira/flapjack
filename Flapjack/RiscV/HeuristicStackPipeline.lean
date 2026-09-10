import Flapjack.RiscV.SpillCosts
import Flapjack.RiscV.WordToStack

/-!
# Heuristic graph allocation to StackLang

The heuristic graph allocator and the location-aware Word-to-Stack lowering
were already available independently.  This module packages their complete
full-SSA composition, retaining the graph allocation and renamed Word body so
the later StackRemove/RISC-V proofs can consume the same witnesses.
-/

namespace Flapjack.RiscV

open Flapjack

def wordAllocateGraphFunctionWithHeuristicsEntryToStack [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width)) (fixedSources : List Nat)
    (algorithm currentFunction colours stackStart : Nat)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState) :
    Option (WordSsaState × List Nat × WordGraphAllocation ×
      WordProg (Word width) × StackProg Nat × WordStackBitmapState) := do
  let (ssaState, renamedParameters, allocation, renamedProgram) ←
    wordAllocateGraphFunctionWithHeuristicsEntryRenamed parameters program
      fixedSources algorithm currentFunction colours stackStart
  let (stackProgram, finalState) ←
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps config
      renamedParameters allocation colours stackStart registerCount bitmapRegister
      frameSlots storeConstsStub bitmapState renamedProgram
  pure (ssaState, renamedParameters, allocation, renamedProgram,
    stackProgram, finalState)

theorem wordAllocateGraphFunctionWithHeuristicsEntryToStack_stack_result
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
    (hbridge : wordAllocateGraphFunctionWithHeuristicsEntryToStack config
      parameters program fixedSources algorithm currentFunction colours stackStart
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState =
      some (ssaState, renamedParameters, allocation, renamedProgram,
        stackProgram, finalState)) :
    wordToStackFunctionWithGraphAllocationAndLocationBitmaps config
      renamedParameters allocation colours stackStart registerCount bitmapRegister
      frameSlots storeConstsStub bitmapState renamedProgram =
      some (stackProgram, finalState) := by
  simp only [wordAllocateGraphFunctionWithHeuristicsEntryToStack] at hbridge
  cases halloc : wordAllocateGraphFunctionWithHeuristicsEntryRenamed
      parameters program fixedSources algorithm currentFunction colours stackStart with
  | none =>
      simp [halloc] at hbridge
  | some allocationResult =>
      cases allocationResult with
      | mk allocationState rest =>
          cases rest with
          | mk allocationParameters rest =>
              cases rest with
              | mk allocation' allocationProgram =>
                  cases hstack : wordToStackFunctionWithGraphAllocationAndLocationBitmaps
                      config allocationParameters allocation' colours stackStart
                      registerCount bitmapRegister frameSlots storeConstsStub bitmapState
                      allocationProgram with
                  | none =>
                      simp [halloc, hstack] at hbridge
                  | some generatedResult =>
                      cases generatedResult with
                      | mk generatedProgram generatedState =>
                          have hresult :
                              allocationState = ssaState ∧
                              allocationParameters = renamedParameters ∧
                              allocation' = allocation ∧
                              allocationProgram = renamedProgram ∧
                              generatedProgram = stackProgram ∧
                              generatedState = finalState := by
                            simpa [halloc, hstack] using hbridge
                          rcases hresult with
                            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
                          exact hstack

end Flapjack.RiscV
