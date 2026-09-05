import Flapjack.Pipeline

namespace Flapjack

example :
    wordAllocateSsaProgramWithSpills
        ({ current := [], next := 10 } : WordSsaState)
        ((.assign 1 (.var 0)) : WordProg Nat) =
      some (({ current := [(1, 10)], next := 11 },
        .assign 10 (.var 0),
        { locations := [(10, .register 12), (0, .register 2)],
          nextSpill := 0 }) : WordSsaState × WordProg Nat × WordSpillState) := by
  simp [wordAllocateSsaProgramWithSpills, wordSsaRenameProgram,
    wordSsaRenameProgramWithLoops, wordSsaRenameExp, wordSsaFresh,
    wordSsaRead, wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordProgVariables, wordAllocateVarsWithSpills,
    wordGreedyAllocateWithSpills, wordUsedLocationRegisters,
    wordColourCandidates, wordFirstAvailable, wordNeighbours,
    wordPreferredRegister, wordRemoveRegisters, wordAllocatableRegisters,
    wordSpillAllocationRespectsClashes, lookupNatInfo,
    wordSpecialArithLocationsSafe, wordProgSpecialLocationsSafe,
    wordExpReadVars, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

example :
    (wordAllocateVarsWithSpills (List.range 29)
      (wordPairwiseClashes (List.range 29))).map
        (fun state => state.nextSpill != 0) = some true := by
  exact wordAllocateVarsWithSpills_spills_example

example (slots : List Nat) (edges : List (Nat × Nat))
    (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpills slots edges = some state)
    (name : Nat) (hname : name ∈ slots.eraseDups) :
    ∃ location, lookupNatInfo name state.locations = some location := by
  exact wordAllocateVarsWithSpills_maps_slots slots edges state hstate name hname

example :
    wordProgSpecialLocationsSafe
        [(0, .stack 0), (1, .register 5), (2, .register 6), (3, .register 7)]
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat) = true := by
  native_decide

example :
    wordProgSpecialLocationsSafe
        [(0, .register 4), (1, .register 5), (2, .register 6),
          (3, .register 7), (4, .register 8)]
        ((.seq (.inst (.arith (.addCarry 0 1 2 3 4))) .skip) : WordProg Nat) = true := by
  native_decide

example :
    wordProgSpecialLocationsSafe
        [(0, .stack 0), (1, .register 5), (2, .stack 1),
          (3, .register 6), (4, .stack 2)]
        ((.inst (.arith (.addCarry 0 1 2 3 4))) : WordProg Nat) = true := by
  native_decide

end Flapjack
