import Flapjack.RiscV.RegAlloc

namespace Flapjack

/-! Regression for CakeML's `full_ssa_cc_trans` function entry sequence. -/

example :
    wordSsaRenameFunctionWithEntry [2, 3]
        (.return 0 [2, 3] : WordProg Nat) =
        ({ current := [(3, 9), (2, 5)], next := 13 },
        [5, 9],
        .seq (.move 1 [(5, 2), (9, 3)])
          (.seq (.move 0 [(2, 5), (4, 9)]) (.return 0 [2, 4]))) := by
  have hAbi : wordSsaCallAbiRegisters 1 2 = [2, 4] := by rfl
  simp [wordSsaRenameFunctionWithEntry, wordSsaEntryMove,
    wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops, wordSsaRead,
    wordSsaFreshList, wordSsaFresh, wordSsaSeq, hAbi, lookupNatInfo]

example :
    (wordSsaEntryMove [2, 3] [5, 9] : WordProg Nat) =
      .move 1 [(5, 2), (9, 3)] := by
  rfl

/- CakeML's `ssa_cc_trans_inst` uses the fixed RISC-V `LongMul` protocol:
   operands enter registers 0 and 4, the multiply writes 6 and 0, and the
   two fresh SSA results leave through the explicit result move. -/
example :
    wordSsaRenameProgram ({ current := [], next := 4 } : WordSsaState)
        (.inst (.arith (.longMul 1 2 2 3)) : WordProg Nat) =
      ({ current := [(2, 8), (1, 4)], next := 12 },
        .seq (.move 1 [(0, 2), (4, 3)])
        (.seq (.inst (.arith (.longMul 6 0 0 4)))
            (.move 1 [(8, 0), (4, 6)]))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRead, wordSsaFresh, wordSsaSeq, lookupNatInfo]

example :
    wordSsaAbiParameters 3 = [0, 2, 4] := by
  rfl

/- Cake's `ssa_cc_trans_inst` routes LongMul through its fixed architectural
   operands and explicitly copies both results back to fresh SSA names. -/
example :
    wordSsaRenameProgram ({ current := [], next := 10 } : WordSsaState)
        (.inst (.arith (.longMul 1 2 3 4)) : WordProg Nat) =
      ({ current := [(2, 14), (1, 10)], next := 18 },
        .seq (.move 1 [(0, 3), (4, 4)])
            (.seq (.inst (.arith (.longMul 6 0 0 4)))
            (.move 1 [(14, 0), (10, 6)]))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRead, wordSsaFresh, wordSsaSeq, lookupNatInfo]

/- CakeML's fresh-name limit scans the body only, so unused ABI formals do not
   move the full-SSA name stream. -/
example :
    wordSsaRenameFunctionWithEntry [0, 2, 4]
        (.skip : WordProg Nat) =
      ({ current := [(4, 13), (2, 9), (0, 5)], next := 17 },
        [5, 9, 13],
        .seq (.move 1 [(5, 0), (9, 2), (13, 4)]) .skip) := by
  simp [wordSsaRenameFunctionWithEntry, wordSsaEntryMove,
    wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaFreshList, wordSsaFresh]

/- Cake's post-SSA dead-move pass removes an unused formal's entry copy. -/
example :
    wordSsaRenameFunctionWithEntryAndDeadMoves [0, 2, 4]
        (.skip : WordProg Nat) =
      ({ current := [(4, 13), (2, 9), (0, 5)], next := 17 },
        [5, 9, 13], .skip) := by
  simp [wordSsaRenameFunctionWithEntryAndDeadMoves,
    wordSsaRenameFunctionWithEntry, wordSsaEntryMove,
    wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordListMaximum, wordProgVariables, wordProgReadVars, wordProgWriteVars,
    wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaFreshList, wordSsaFresh]

/- A formal used by the renamed body remains in the entry move. -/
def liveEntryMovesRemain : Bool :=
  match (wordSsaRenameFunctionWithEntryAndDeadMoves [0, 2]
      (.return 0 [0, 2] : WordProg Nat)).2.2 with
  | .seq (.move _ moves) _ => moves == [(5, 0), (9, 2)]
  | _ => false

#guard liveEntryMovesRemain

example :
    wordFullSsaCcTrans 2
        (.return 0 [0, 2] : WordProg Nat) =
      wordSsaRenameFunctionWithEntry [0, 2]
        (.return 0 [0, 2] : WordProg Nat) := by
  exact wordFullSsaCcTrans_eq_named_entry 2 _


/- The FFI SSA boundary refreshes the live cut set around the ABI call and
   restores it afterwards, matching CakeML's `ssa_cc_trans` shape. -/
example :
    wordSsaRenameProgram ({ current := [], next := 10 } : WordSsaState)
      (.ffi "f" 1 2 3 4 ([5], [6]) : WordProg Nat) =
      ({ current := [(6, 26), (5, 22)], next := 30 },
        .seq (.move 0 [(12, 5), (16, 6)])
          (.seq (.move 1 [(2, 1), (4, 2), (6, 3), (8, 4)])
            (.seq (.ffi "f" 2 4 6 8 ([12], [16]))
              (.move 0 [(22, 12), (26, 16)])))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, wordSsaReadCutsets, wordSsaFreshList,
    wordSsaFresh, wordSsaRead, wordSsaRestrict, wordSsaSeq, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop, lookupNatInfo,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert,
    NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList]

/- The entry-aware graph boundary accepts an unused ABI formal and returns a
   coloured program containing its setup move. -/
example :
    (wordAllocateGraphFunctionWithEntry [2]
      (.skip : WordProg (RiscV.Word 64)) [2] 13 0).isSome := by
  decide +kernel

example :
    (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferences [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

example :
    (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesFixed [2]
      (.skip : WordProg (RiscV.Word 64))).isSome := by
  decide +kernel

#guard wordAllocateVarsWithFixedSources [2, 5] [] [] [2] =
  some { locations := [(5, .register 7), (2, .register 2)], nextSpill := 0 }

example (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources [2, 5] [] [] [2] = some state) :
    lookupNatInfo 2 state.locations = some (.register 2) := by
  exact wordAllocateVarsWithFixedSources_preserves_fixed_source
    [2, 5] [] [] [2] state hstate 2 (by simp)

example (state : WordSpillState)
    (hstate : wordAllocateVarsWithFixedSources [2, 5] [] [] [2] = some state) :
    ∀ name, name ∈ [2, 5].eraseDups →
      ∃ location, lookupNatInfo name state.locations = some location := by
  exact wordAllocateVarsWithFixedSources_maps_slots
    [2, 5] [] [] [2] state hstate

end Flapjack
