import Flapjack.RiscV.CorrectnessStackFunctionEntry

/-!
# Bitmap-aware spill function-entry composition

The spill-aware entrypoint changes only the location map supplied to the
bitmap-aware Word-to-Stack pass.  This theorem exposes the same sequential
entry/body evaluator boundary after that adapter, so allocator clients can
reuse the function-entry composition contract without unfolding the adapter.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_wordToStackFunctionWithSpillStateAndLocationBitmaps
    [NeZero width]
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
  simpa [wordToStackFunctionWithSpillStateAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps, hbody, hmoves] using
    (evalWordStackMachine_wordStackJoin state middle final moves body
      hentry hbodyEval)

end Flapjack.RiscV
