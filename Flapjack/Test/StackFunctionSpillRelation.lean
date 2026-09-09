import Flapjack.RiscV.CorrectnessStackFunctionSpill

/-! Regression coverage for the bitmap-aware spill function-entry adapter. -/

namespace Flapjack.RiscV

example [NeZero width]
    (config : WordStackConfig) (parameters : List Nat)
    (allocation : WordSpillState)
    (registerCount bitmapRegister frameSlots : Nat)
    (storeConstsStub : Option Nat) (bitmapState bitmapFinal : WordStackBitmapState)
    (program : WordProg (Word width))
    (body moves : StackProg Nat)
    (state middle final : WordStackMachineState width)
    (hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState program =
      some (body, bitmapFinal))
    (hmoves : wordStackMovesFromPhysical
      { config with locations := allocation.locations } parameters 2 = some moves)
    (hentry : evalWordStackMachine state moves = some middle)
    (hbodyEval : evalWordStackMachine middle body = some final) :
    evalWordStackMachine state
      (((wordToStackFunctionWithSpillStateAndLocationBitmaps config parameters
        allocation registerCount bitmapRegister frameSlots storeConstsStub
        bitmapState program).map Prod.fst).getD .skip) =
      some final := by
  exact evalWordStackMachine_wordToStackFunctionWithSpillStateAndLocationBitmaps
    config parameters allocation registerCount bitmapRegister frameSlots
    storeConstsStub bitmapState bitmapFinal program body moves state middle final
    hbody hmoves hentry hbodyEval

end Flapjack.RiscV
