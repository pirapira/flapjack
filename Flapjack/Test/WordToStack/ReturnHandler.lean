import Flapjack.RiscV.WordToStack

/-! The SSA allocator stores the complete continuation in a call's return
    metadata.  This regression prevents the Word-to-Nat adapter from erasing
    that continuation before Word-to-Stack lowering sees it. -/

namespace Flapjack.RiscV

def returnHandlerConversionProgram : WordProg (Word 64) :=
  .seq (.move 0 [(2, 4)]) (.return 0 [2])

def returnHandlerCodeConfig : WordStackConfig :=
  { locations := [(7, .register 5)]
    scratch := 31
    stackBase := 10 }

def returnHandlerNatProgram : WordProg Nat :=
  .assign 7 (.const 9)

example :
    wordProgToNat
        (.call (some ([2], ([], []), returnHandlerConversionProgram, 7, 8))
          (some 3) [] none : WordProg (Word 64)) =
      .call
        (some ([2], ([], []), wordProgToNat returnHandlerConversionProgram, 7, 8))
        (some 3) [] none := by
  simp [wordProgToNat]

example :
    wordStackEmbeddedReturnCode returnHandlerCodeConfig
      (some ([2], ([], []), returnHandlerNatProgram, 7, 8)) =
      some (.const 5 9) := by
  simp [wordStackEmbeddedReturnCode, wordToStackProgNat,
    wordStackCompileExpNat, wordStackWritePhysicalNat,
    wordStackLocation, lookupNatInfo, returnHandlerCodeConfig,
    returnHandlerNatProgram]

example :
    wordToStackProgNat returnHandlerCodeConfig
      (.call (some ([7], ([], []), returnHandlerNatProgram, 12, 13))
        (some 3) [] none) =
      some (wordToStackCallNoHandler false 3 0 0 31 [7]
        (.const 5 9) 12 13) := by
  simp [wordToStackProgNat,
    wordStackCompileExpNat, wordStackWritePhysicalNat,
    wordStackLocation, lookupNatInfo, wordStackMovesToPhysical,
    wordStackPhysicalMovesTo, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    wordStackLocationMoveRemoveDestination, wordStackLocationMove,
    wordStackJoin,
    returnHandlerCodeConfig, returnHandlerNatProgram]

example :
    wordProgToNat
        (.call none (some 3) []
          (some (9, returnHandlerConversionProgram, 10, 11)) : WordProg (Word 64)) =
      .call none (some 3) []
        (some (9, wordProgToNat returnHandlerConversionProgram, 10, 11)) := by
  simp [wordProgToNat]

end Flapjack.RiscV
