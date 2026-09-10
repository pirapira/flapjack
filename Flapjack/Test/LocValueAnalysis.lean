import Flapjack.RiscV.Allocator

/-! CakeML's WordLang `LocValue` materializes a code label.  The label is not
    a source register: only the destination participates in SSA, liveness,
    preferences, and clash colouring. -/

namespace Flapjack.RiscV

example :
    wordProgReadVars (.locValue 7 100 : WordProg Nat) = [] := by
  rfl

example :
    wordProgPreferenceEdges (.locValue 7 100 : WordProg Nat) = [] := by
  rfl

example :
    wordClashTree (.locValue 7 100 : WordProg Nat) [] =
      .delta [7] [] := by
  simp [wordClashTree]

example :
    wordSsaRenameProgram
      ({ current := [], next := 10 } : WordSsaState)
      (.locValue 3 100 : WordProg Nat) =
      ({ current := [(3, 10)], next := 14 },
        .locValue 10 100) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaFresh]

example :
    wordApplyColour (fun name => name + 1)
      (.locValue 3 100 : WordProg Nat) =
      .locValue 4 100 := by
  simp [wordApplyColour]

end Flapjack.RiscV
