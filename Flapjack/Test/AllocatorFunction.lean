import Flapjack.Pipeline

namespace Flapjack

/-! Regression tests for the CakeML-style function boundary around SSA
    renaming and ABI parameter entry moves. -/

example :
    wordSsaRenameFunction [2, 3]
        (.return 0 [2, 3] : WordProg Nat) =
      ({ current := [(3, 6), (2, 5)], next := 7 },
        [5, 6], .return 0 [5, 6]) := by
  simp [wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRead,
    wordSsaFreshList, wordSsaFresh, lookupNatInfo]

/- An unused formal is still included in the allocation input, because the
   generated entry move must have a destination. -/
example :
    (wordAllocateSsaFunctionWithSpills [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  native_decide

end Flapjack
