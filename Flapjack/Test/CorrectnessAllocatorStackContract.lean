import Flapjack.RiscV.CorrectnessAllocatorStackContract

/-! Regression coverage for the combined allocator-to-StackLang contract. -/

namespace Flapjack.RiscV

example [NeZero width]
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
  have hcontract := wordAllocateSsaFunctionWithEntryAndSpillToStack_contract
    config parameters program registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState ssaState renamedParameters renamedProgram allocation stackProgram
    finalState body moves machineState middle final bodyState hbridge hbody hmoves
    hentry hbodyEval
  exact hcontract.2.2.2.2.2.2.2.2.2

end Flapjack.RiscV
