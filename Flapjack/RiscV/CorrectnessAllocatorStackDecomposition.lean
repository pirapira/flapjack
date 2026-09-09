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
    ∃ body moves bitmapFinal,
      wordToStackProgWordWithLocationBitmaps
        { config with locations := allocation.locations }
        registerCount bitmapRegister frameSlots storeConstsStub bitmapState
        renamedProgram = some (body, bitmapFinal) ∧
      wordStackMovesFromPhysical
        { config with locations := allocation.locations } renamedParameters 2 =
        some moves ∧
      stackProgram = wordStackJoin moves body ∧
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
          cases hmoves : wordStackMovesFromPhysical
              { config with locations := allocation.locations } renamedParameters 2 with
          | none => simp [hbody, hmoves] at hstack
          | some moves =>
              have hresult :
                  (wordStackJoin moves body, bitmapFinal) =
                    (stackProgram, finalState) := by
                simpa [hbody, hmoves] using hstack
              have hprogram : wordStackJoin moves body = stackProgram :=
                congrArg Prod.fst hresult
              have hbitmap : bitmapFinal = finalState :=
                congrArg Prod.snd hresult
              exact ⟨body, moves, bitmapFinal, rfl, rfl,
                hprogram.symm, hbitmap⟩

end Flapjack.RiscV
