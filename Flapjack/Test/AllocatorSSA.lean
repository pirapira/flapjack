import Flapjack.Pipeline

namespace Flapjack

example :
    wordSsaRenameLinear
        { current := [(2, 100), (3, 101), (4, 102)], next := 200 }
        [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      ({ current := [(6, 203), (5, 202), (1, 201), (0, 200),
          (2, 100), (3, 101), (4, 102)], next := 204 },
        [.arith (.addCarry 200 201 100 101 102),
          .arith (.addCarry 202 203 200 201 100)]) := by
  exact wordSsaRenameLinear_addCarry

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.shareInst .load 1
          (.op .add [.var 2, .const (4 : Nat)])) : WordProg Nat) =
      ({ current := [(1, 200), (2, 100)], next := 201 },
        .shareInst .load 200 (.op .add [.var 100, .const 4])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp, wordSsaFresh, wordSsaRead, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.call (some ([3, 4], [2])) (some 7) [2, 5] none) : WordProg Nat) =
      ({ current := [(4, 201), (3, 200), (2, 100)], next := 202 },
        .call (some ([200, 201], [100])) (some 7) [100, 5] none) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameReturns, wordSsaFreshList, wordSsaFresh, wordSsaRead,
    lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.seq (.locValue 3 2) (.return 0 [3])) : WordProg Nat) =
        ({ current := [(3, 200), (2, 100)], next := 201 },
        .seq (.locValue 200 100) (.return 0 [200])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaFresh, wordSsaRead, lookupNatInfo]

example :
    wordProgReadVars
        ((.call (some ([5], [6])) (some 7) [8]
          (some (9, .return 0 [10])) : WordProg Nat)) = [8, 6, 10] := by
  rfl

example :
    wordProgWriteVars
        ((.call (some ([5], [6])) (some 7) [8]
          (some (9, .return 0 [10])) : WordProg Nat)) = [5, 9] := by
  rfl

example :
    (wordSsaRenameProgram
        ({ current := [(1, 100)], next := 200 } : WordSsaState)
      ((.loop [1] (.seq (.assign 1 (.var 1)) (.break 0)) [1]) :
          WordProg Nat)).1 =
      { current := [(1, 200)], next := 201 } := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRefreshList, wordSsaRestrict, wordSsaFresh,
    wordSsaFindLoopFrame, wordSsaReconcileTo, wordSsaRead,
    wordSsaSeq, lookupNatInfo, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

end Flapjack
