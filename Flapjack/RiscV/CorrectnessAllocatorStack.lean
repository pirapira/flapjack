import Flapjack.RiscV.CorrectnessStackFunctionSpill
import Flapjack.RiscV.AllocatorBridgeCorrectness

/-!
# Allocator-output StackLang simulation boundary

The full-SSA spill allocator returns the renamed program, its location map,
and the generated StackLang function together.  This file exposes the
execution contract at that package boundary: once the bitmap-aware body and
entry moves have been evaluated, the packaged StackLang program evaluates to
the same final machine state.
-/

namespace Flapjack.RiscV

theorem wordAllocateSsaFunctionWithEntryAndSpillToStack_stack_result
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
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
    wordToStackFunctionWithSpillStateAndLocationBitmaps config renamedParameters
      allocation registerCount bitmapRegister frameSlots storeConstsStub state
      renamedProgram = some (stackProgram, finalState) := by
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
                            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
                          exact hstack

theorem evalWordStackMachine_wordAllocateSsaFunctionWithEntryAndSpillToStack
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg (Word width)) (allocation : WordSpillState)
    (stackProgram : StackProg Nat) (finalState : WordStackBitmapState)
    (body moves : StackProg Nat)
    (machineState middle final : WordStackMachineState width)
    (bodyState : WordStackBitmapState)
    (hbridge : wordAllocateSsaFunctionWithEntryAndSpillToStack config parameters
      program registerCount bitmapRegister frameSlots storeConstsStub bitmapState =
      some (ssaState, renamedParameters, renamedProgram, allocation,
        stackProgram, finalState))
    (hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState
      renamedProgram = some (body, bodyState))
    (hmoves : wordStackMovesFromPhysical
      { config with locations := allocation.locations } renamedParameters 2 =
      some moves)
    (hentry : evalWordStackMachine machineState moves = some middle)
    (hbodyEval : evalWordStackMachine middle body = some final) :
    evalWordStackMachine machineState stackProgram = some final := by
  have hstack := wordAllocateSsaFunctionWithEntryAndSpillToStack_stack_result
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState hbridge
  have hsimulation :=
    evalWordStackMachine_wordToStackFunctionWithSpillStateAndLocationBitmaps
      config renamedParameters allocation registerCount bitmapRegister frameSlots
      storeConstsStub bitmapState bodyState renamedProgram body moves machineState
      middle final hbody hmoves hentry hbodyEval
  simpa [hstack] using hsimulation

end Flapjack.RiscV
