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
  simpa [wordToStackFunctionWithSpillStateAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps, hbody] using hbodyEval

theorem wordToStackFunctionWithSpillStateAndLocationBitmaps_preserves_bitmap_length
    [NeZero width]
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
  simp only [wordToStackFunctionWithSpillStateAndLocationBitmaps,
    wordToStackFunctionWithParametersAndLocationBitmaps] at hresult
  cases hbody : wordToStackProgWordWithLocationBitmaps
      { config with locations := allocation.locations }
      registerCount bitmapRegister frameSlots storeConstsStub bitmapState program with
  | none =>
      rw [hbody] at hresult
      simp at hresult
  | some bodyResult =>
      cases bodyResult with
      | mk body bodyState =>
              have hpair :
                  (body, bodyState) = (stackProgram, finalState) := by
                simpa [hbody] using hresult
              have hbitmap : bodyState = finalState :=
                congrArg Prod.snd hpair
              have hinner :
                  wordToStackProgNatWithBitmapBuilder
                    { config with locations := allocation.locations }
                    (wordStackLiveBitmapFromLocations
                      { config with locations := allocation.locations }
                      frameSlots width)
                    registerCount bitmapRegister frameSlots width storeConstsStub
                    bitmapState (wordProgToNat program) =
                    some (body, bodyState) := by
                simpa [wordToStackProgWordWithLocationBitmaps,
                  wordToStackProgNatWithLocationBitmaps] using hbody
              have hbodyLength :=
                wordToStackProgNatWithBitmapBuilder_preserves_length
                  { config with locations := allocation.locations }
                  (wordStackLiveBitmapFromLocations
                    { config with locations := allocation.locations }
                    frameSlots width)
                  registerCount bitmapRegister frameSlots width storeConstsStub
                  bitmapState (wordProgToNat program) hstate body bodyState hinner
              rw [← hbitmap]
              exact hbodyLength

end Flapjack.RiscV
