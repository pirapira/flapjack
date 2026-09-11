import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for state-threaded handler lowering. -/

namespace Flapjack.RiscV

def handlerLoweringConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    stackBase := 10
    returnLabel := 20
    entryLabel := 21
    handlerLabel := 30 }

def handlerLoweringInitial : WordStackBitmapState :=
  wordStackInitialBitmaps false

def handlerLoweringBody : WordProg Nat :=
  .seq .skip (.raise 0)

example :
    wordToStackProgNatWithBitmapBuilder handlerLoweringConfig (fun live => live)
      2 26 0 64 none handlerLoweringInitial
      (.call (some ([], ([], []), .skip, 0, 0)) (some 7) []
        (some (1, handlerLoweringBody, 30, 21))) =
      some (wordToStackCallWithHandlerInSection false 7 0 0 31 .skip
        (.seq .skip (.call none (.label 0) none))
          (wordStackReturnLabel handlerLoweringConfig
            (some ([], ([], []), .skip, 0, 0)))
          (wordStackEntryLabel handlerLoweringConfig
            (some ([], ([], []), .skip, 0, 0)))
          (wordStackHandlerLabel handlerLoweringConfig 30)
          (wordStackHandlerEntryLabel handlerLoweringConfig 21) 1,
        handlerLoweringInitial) := by
  have h := wordToStackProgNatWithBitmapBuilder_call_handler
    (config := handlerLoweringConfig) (bitmapBuilder := fun live => live)
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 0)
    (wordBits := 64) (storeConstsStub := none)
    (state := handlerLoweringInitial) (liveState := handlerLoweringInitial)
    (returnState := handlerLoweringInitial) (finalState := handlerLoweringInitial)
    (returns := some ([], ([], []), .skip, 0, 0)) (target := 7)
    (arguments := []) (exception := 1) (handlerLabel := 30) (entryLabel := 21)
    (body := handlerLoweringBody) (argumentMoves := .skip) (liveCode := .skip)
    (returnCode := .skip)
    (handlerCode := .seq .skip (.call none (.label 0) none))
    (hargs := by
      simp [handlerLoweringConfig, wordStackMovesToPhysical,
        wordStackPhysicalMovesTo, wordStackParallelLocationMove,
        wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
        wordStackLocationMoveRemoveDestination, wordStackLocationMove])
    (hlive := by
      simp [handlerLoweringConfig, handlerLoweringInitial, wordStackCallLiveBitmap,
        wordStackBitmapWriteWithBuilder])
    (hreturnSome := by
      intro returnData hreturn
      cases hreturn
      simp [wordToStackProgNatWithBitmapBuilder, wordToStackProgNat, handlerLoweringInitial])
    (hreturnNone := by simp)
    (hhandler := by
      simp [handlerLoweringConfig, handlerLoweringInitial,
        handlerLoweringBody, wordToStackProgNatWithBitmapBuilder,
        wordToStackProgNat, wordToStackRaise, stackRaiseStubLocation])
  simpa [wordStackJoin, handlerLoweringConfig] using h

end Flapjack.RiscV
