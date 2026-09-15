import Flapjack.RiscV.CorrectnessAllocatorStack

/-!
# Decomposition of the allocator's StackLang result

The allocator bridge packages the bitmap-aware body and physical entry moves
into one StackLang program.  This theorem recovers those components and their
join equation from a successful executable result, which is the shape needed
by subsequent RISC-V simulation proofs.
-/

namespace Flapjack.RiscV

theorem wordAllocateSsaFunctionWithEntryAndSpillToStack_decompose
    [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (program : WordProg (Word width))
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState : WordStackBitmapState)
    (ssaState : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg (Word width)) (allocation : WordSpillState)
    (stackProgram : StackProg Nat) (finalState : WordStackBitmapState)
    (hbridge : wordAllocateSsaFunctionWithEntryAndSpillToStack config parameters
      program registerCount bitmapRegister frameSlots storeConstsStub bitmapState =
      some (ssaState, renamedParameters, renamedProgram, allocation,
        stackProgram, finalState)) :
    ∃ body bitmapFinal,
      wordToStackProgWordWithLocationBitmaps
        { config with locations := allocation.locations }
        registerCount bitmapRegister frameSlots storeConstsStub bitmapState
        renamedProgram = some (body, bitmapFinal) ∧
      stackProgram = body ∧
      bitmapFinal = finalState := by
  have hstack := wordAllocateSsaFunctionWithEntryAndSpillToStack_stack_result
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState hbridge
  simp only [wordToStackFunctionWithSpillStateAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps] at hstack
  cases hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState
      renamedProgram with
  | none => simp [hbody] at hstack
  | some bodyResult =>
      cases bodyResult with
      | mk body bitmapFinal =>
          have hresult : (body, bitmapFinal) = (stackProgram, finalState) := by
            simpa [hbody] using hstack
          have hprogram : body = stackProgram := congrArg Prod.fst hresult
          have hbitmap : bitmapFinal = finalState := congrArg Prod.snd hresult
          exact ⟨body, bitmapFinal, rfl, hprogram.symm, hbitmap⟩

end Flapjack.RiscV
