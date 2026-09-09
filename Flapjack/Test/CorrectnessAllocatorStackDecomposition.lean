import Flapjack.RiscV.CorrectnessAllocatorStackDecomposition

/-! Regression coverage for decomposition of an allocator-produced StackLang program. -/

namespace Flapjack.RiscV

example [NeZero width]
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
  exact wordAllocateSsaFunctionWithEntryAndSpillToStack_decompose
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState hbridge

end Flapjack.RiscV
