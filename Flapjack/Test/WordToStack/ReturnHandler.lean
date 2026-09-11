import Flapjack.RiscV.WordToStack

/-! The SSA allocator stores the complete continuation in a call's return
    metadata.  This regression prevents the Word-to-Nat adapter from erasing
    that continuation before Word-to-Stack lowering sees it. -/

namespace Flapjack.RiscV

def returnHandlerConversionProgram : WordProg (Word 64) :=
  .seq (.move 0 [(2, 4)]) (.return 0 [2])

example :
    wordProgToNat
        (.call (some ([2], ([], []), returnHandlerConversionProgram, 7, 8))
          (some 3) [] none : WordProg (Word 64)) =
      .call
        (some ([2], ([], []), wordProgToNat returnHandlerConversionProgram, 7, 8))
        (some 3) [] none := by
  simp [wordProgToNat]

example :
    wordProgToNat
        (.call none (some 3) []
          (some (9, returnHandlerConversionProgram, 10, 11)) : WordProg (Word 64)) =
      .call none (some 3) []
        (some (9, wordProgToNat returnHandlerConversionProgram, 10, 11)) := by
  simp [wordProgToNat]

end Flapjack.RiscV
