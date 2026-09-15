import Flapjack.RiscV.CorrectnessStackFunctionSpill

/-! Regression coverage for the bitmap-aware spill function-entry adapter. -/

namespace Flapjack.RiscV

example [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordSpillState)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState bitmapFinal : WordStackBitmapState)
    (program : WordProg (Word width))
    (body : StackProg Nat)
    (state final : WordStackMachineState width)
    (hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState program =
      some (body, bitmapFinal))
    (hbodyEval : evalWordStackMachine state body = some final) :
    evalWordStackMachine state
      (((wordToStackFunctionWithSpillStateAndLocationBitmaps config parameters
        allocation registerCount bitmapRegister frameSlots storeConstsStub
        bitmapState program).map Prod.fst).getD .skip) =
      some final := by
  exact evalWordStackMachine_wordToStackFunctionWithSpillStateAndLocationBitmaps
    config parameters allocation registerCount bitmapRegister frameSlots
    storeConstsStub bitmapState bitmapFinal program body state final
    hbody hbodyEval

example [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordSpillState)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState finalState : WordStackBitmapState)
    (program : WordProg (Word width)) (stackProgram : StackProg Nat)
    (hstate : bitmapState.length = bitmapState.data.length)
    (hresult : wordToStackFunctionWithSpillStateAndLocationBitmaps config parameters
      allocation registerCount bitmapRegister frameSlots storeConstsStub bitmapState
      program = some (stackProgram, finalState)) :
    finalState.length = finalState.data.length := by
  exact wordToStackFunctionWithSpillStateAndLocationBitmaps_preserves_bitmap_length
    config parameters allocation registerCount bitmapRegister frameSlots storeConstsStub
    bitmapState finalState program stackProgram hstate hresult

end Flapjack.RiscV
