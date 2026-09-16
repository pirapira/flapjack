import Flapjack.Pipeline
import Flapjack.WordSemantics

namespace Flapjack

open RiscV

example :
    wordSsaRenameLinear (α := Nat)
        { current := [(2, 100), (3, 101), (4, 102)], next := 200 }
        [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      ({ current := [(6, 212), (5, 208), (1, 204), (0, 200),
          (2, 100), (3, 101), (4, 102)], next := 216 },
        [.arith (.addCarry 200 204 100 101 102),
          .arith (.addCarry 208 212 200 204 100)]) := by
  exact wordSsaRenameLinear_addCarry

example :
    wordInstForcedClashes (α := Nat)
        (.arith (.longMul 0 1 2 3)) =
      [(0, 1), (0, 2), (0, 3)] := by
  rfl

example :
    wordInstForcedClashes (α := Nat)
        (.arith (.addCarry 0 1 2 3 4)) =
      [(0, 1), (0, 2), (0, 3)] := by
  rfl

example :
    wordProgAtomicClashes
        ((.inst (.arith (.longMul 0 1 2 3))) : WordProg Nat) [] =
      [(0, 1), (0, 2), (0, 3)] := by
  rfl

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.shareInst .load 1
          (.op .add [.var 2, .const (4 : Nat)])) : WordProg Nat) =
      ({ current := [(1, 200), (2, 100)], next := 204 },
        .shareInst .load 200 (.op .add [.var 100, .const 4])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp, wordSsaFresh, wordSsaRead, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.call (some ([3, 4], ([2], []), .skip, 0, 0)) (some 7) [2, 5] none) : WordProg Nat) =
      ({ current := [(4, 216), (3, 212), (2, 208)], next := 220 },
        .seq (.move 0 [(202, 100)])
          (.seq (.move 1 [(2, 100), (4, 5)])
            (.call (some ([2, 4], ([202], []),
              .seq (.move 0 [(208, 202)])
                (.move 1 [(212, 2), (216, 4)]), 0, 0))
              (some 7) [2, 4] none))) := by
  have hAbi : wordSsaCallAbiRegisters 1 2 = [2, 4] := by rfl
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, hAbi,
    wordSsaFreshList, wordSsaFresh, wordSsaRead, lookupNatInfo,
    wordSsaReadCutsets, wordSsaRestrict, wordSsaSeq, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert,
    NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.seq (.locValue 3 2) (.return 0 [3])) : WordProg Nat) =
        ({ current := [(3, 200), (2, 100)], next := 204 },
        .seq (.locValue 200 2)
          (.seq (.move 0 [(2, 200)]) (.return 0 [2]))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaCallAbiRegisters, wordSsaFresh, wordSsaRead, wordSsaSeq,
    lookupNatInfo]

example :
    wordProgReadVars
        ((.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8]
        (some (9, .return 0 [10], 0, 0)) : WordProg Nat)) = [8, 6, 0, 10] := by
  rfl

example :
    wordProgWriteVars
        ((.call (some ([5], ([6], []), .skip, 0, 0)) (some 7) [8]
          (some (9, .return 0 [10], 0, 0)) : WordProg Nat)) = [5, 9] := by
  rfl

example :
    wordSsaRenameProgram
        ({ current := [(1, 100)], next := 200 } : WordSsaState)
        ((.call (some ([2], ([1], []), .skip, 0, 0)) (some 7) [1]
          (some (3, .assign 4 (.var 1), 0, 0)) : WordProg Nat)) =
        ({ current := [(3, 232), (4, 228), (2, 224), (1, 208)], next := 236 },
        .seq (.move 0 [(202, 100)])
          (.seq (.move 1 [(2, 100)])
            (.call (some ([2], ([202], []),
              .seq
                (.seq (.move 0 [(208, 202)]) (.move 1 [(212, 2)]))
                (.seq
                  (.seq (.move 1 [(224, 212)]) (.assign 228 (.const 0)))
                  (.assign 232 (.const 0))), 0, 0))
              (some 7) [2]
              (some (2,
                .seq
                  (.seq (.move 0 [(208, 202)])
                    (.seq (.move 1 [(216, 2)])
                      (.assign 220 (.var 208))))
                  (.seq
                    (.seq (.assign 224 (.const 0)) (.move 1 [(228, 220)]))
                    (.move 1 [(232, 216)])), 0, 0))))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, wordSsaCallAbiRegisters,
    wordSsaReadCutsets, wordSsaRestrict, wordSsaFreshList,
    wordSsaFresh, wordSsaRenameExp, wordSsaRead, wordSsaKeys,
    wordSsaFixInconsistencies, wordSsaPriorityMove, wordSsaBranchPriority,
    wordSsaMergeMoves, wordSsaFakeInconsistencyMoves, wordSsaForceRename,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert, NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList,
    wordSsaSeq, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    let originalState :=
      RiscV.writeRegister (RiscV.zeroState 64) 1 (BitVec.ofNat 64 42)
    let renamedState :=
      RiscV.writeRegister (RiscV.zeroState 64) 100 (BitVec.ofNat 64 42)
    let functions : List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
      [(7, [], .raise 3)]
    let original : WordProg (RiscV.Word 64) :=
      .call (some ([2], ([1], []), .skip, 0, 0)) (some 7) [1]
        (some (3, .assign 4 (.var 1), 0, 0))
    let renamed : WordProg (RiscV.Word 64) :=
      .call (some ([200], ([100], []), .skip, 0, 0)) (some 7) [100]
        (some (201,
          .seq (.assign 202 (.var 100))
            (.assign 200 (.var 2)), 0, 0))
    (evalWordFunctionWithHandlers functions 2 originalState original).map
        (fun result => match result with
          | .normal state => RiscV.readRegister state 4
          | _ => 0) =
      (evalWordFunctionWithHandlers functions 2 renamedState renamed).map
        (fun result => match result with
          | .normal state => RiscV.readRegister state 202
          | _ => 0) := by
  decide +kernel

example :
    (wordSsaRenameProgram
        ({ current := [(1, 100)], next := 200 } : WordSsaState)
      ((.loop [1] (.seq (.assign 1 (.var 1)) (.break 0)) [1]) :
          WordProg Nat)).1 =
      { current := [(1, 200)], next := 208 } := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaLoopSetup, wordSsaFakeMoves,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert, NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList, wordSsaListNextVarRenameMove,
    wordSsaFreshList, wordSsaRestrict, wordSsaFresh,
    wordSsaFindLoopFrame, wordSsaReconcileTo, wordSsaRead,
    wordSsaSeq, lookupNatInfo, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

example :
    wordSsaRenameProgram
        ({ current := [(3, 100)], next := 200 } : WordSsaState)
      ((.raise 3 : WordProg Nat)) =
      ({ current := [(3, 100)], next := 200 },
        .seq (.move 1 [(2, 100)]) (.raise 2)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRead, wordSsaSeq, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(1, 100), (2, 104), (3, 108), (4, 112)], next := 200 } :
          WordSsaState)
      ((.install 1 2 3 4 ([1], [2]) : WordProg Nat)) =
      ({ current := [(2, 220), (1, 216), (202, 212)], next := 224 },
        .seq (.move 0 [(202, 100), (206, 104)])
          (.seq (.move 1 [(2, 202), (4, 206)])
            (.seq (.install 2 4 108 112 ([202], [206]))
              (.seq (.move 1 [(212, 2)])
                (.move 0 [(216, 202), (220, 206)]))))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, wordSsaReadCutsets, wordSsaRestrict,
    wordSsaFreshList, wordSsaFresh, wordSsaRead, wordSsaSeq,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop, lookupNatInfo,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert,
    NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList]

example :
    wordSsaRenameProgram
        ({ current := [(1, 100), (2, 104), (3, 108), (4, 112)], next := 200 } :
          WordSsaState)
      ((.storeConsts 1 2 3 4 [] : WordProg Nat)) =
      ({ current := [(3, 204), (4, 200), (1, 100), (2, 104)], next := 208 },
        .seq (.move 1 [(4, 108), (6, 112)])
          (.seq (.storeConsts 0 2 4 6 [])
            (.move 1 [(204, 4), (200, 6)]))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaFresh, wordSsaRead, wordSsaSeq, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [], next := 10 } : WordSsaState)
      ((.loop [1] (.break 0) []) : WordProg Nat) =
      ({ current := [], next := 14 },
        .seq (.seq (.assign 10 (.const 0)) (.move 0 []))
          (.loop [10] (.break 0) [])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaLoopSetup, wordSsaFakeMoves,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert, NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList, wordSsaListNextVarRenameMove,
    wordSsaFreshList, wordSsaRestrict, wordSsaFresh,
    wordSsaFindLoopFrame, wordSsaReconcileTo, wordSsaRead,
    wordSsaSeq, lookupNatInfo, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

example :
    wordSsaRenameProgram
        ({ current := [(1, 100)], next := 200 } : WordSsaState)
      ((.alloc 3 ([1], []) : WordProg Nat)) =
      ({ current := [(1, 208)], next := 212 },
        .seq (.move 0 [(202, 100)])
          (.seq (.move 1 [(2, 3)])
            (.seq (.alloc 2 ([202], []))
              (.move 0 [(208, 202)])))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaListNextVarRenameMove, wordSsaReadCutsets, wordSsaRestrict,
    wordSsaFreshList, wordSsaFresh, wordSsaRead, wordSsaSeq,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop, lookupNatInfo,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert,
    NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList]

example :
    wordSsaRenameProgram
        ({ current := [(1, 100)], next := 200 } : WordSsaState)
        ((.move 7 [(2, 1), (3, 2)]) : WordProg Nat) =
        ({ current := [(1, 200), (3, 204), (2, 200)], next := 208 },
        .move 7 [(200, 100), (204, 2)]) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameMove, wordSsaFreshList, wordSsaFresh, wordSsaRead,
    wordSsaForceRename, lookupNatInfo]

example :
    wordProgReadVars
        ((.move 7 [(2, 1), (3, 2)]) : WordProg Nat) = [1, 2] := by
  rfl

example :
    wordProgWriteVars
        ((.move 7 [(2, 1), (3, 2)]) : WordProg Nat) = [2, 3] := by
  rfl

example :
    wordProgPreferenceEdges
        ((.move 7 [(2, 1), (3, 2)]) : WordProg Nat) = [(2, 1), (3, 2)] := by
  rfl

example :
    wordSsaRenameProgram
        ({ current := [], next := 10 } : WordSsaState)
        ((.ite .equal 0 (.reg 0)
          (.assign 1 (.var 0)) .skip) : WordProg Nat) =
      ({ current := [(1, 14)], next := 18 },
        .ite .equal 0 (.reg 0)
          (.seq (.assign 10 (.var 0)) (.move 1 [(14, 10)]))
          (.assign 14 (.const 0))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp, wordSsaRenameRegImm, wordSsaRead, wordSsaFresh,
    wordSsaKeys, wordSsaSeq, wordSsaFixInconsistencies,
    wordSsaPriorityMove, wordSsaBranchPriority, wordSsaMergeMoves,
    wordSsaFakeInconsistencyMoves, wordSsaForceRename,
    NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert, NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList, List.eraseDups,
    List.eraseDupsBy, List.eraseDupsBy.loop, lookupNatInfo]

example :
    wordSsaReconcileTo
        ({ current := [(1, 10)], next := 14 } : WordSsaState)
        ({ current := [(1, 14)], next := 18 } : WordSsaState) [1, 2] =
      (.move 1 [(14, 10)] : WordProg Nat) := by
  simp [wordSsaReconcileTo, NumSet.fromList, NumSet.toAList, NumSet.toSet, NumSet.insert, NumSet.insertFuel, NumSet.lrnext, NumSet.lrnextFuel, NumSet.insertList,
    List.filterMap, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop,
    lookupNatInfo]

/-- CakeML's `ssa_cc_trans (Move pri ls)` force-renames every move source that
    is not itself one of the move destinations: `force = FILTER (λ(x,y). ¬ MEM x
    ls_1) (ZIP(ls_2,ren_ls1))` with `ls_1` the destination list (`word_allocScript.sml:348-360`).
    The filter must therefore test the SOURCE (`move.1.2`); testing the
    destination made it vacuous and left `force_rename` dead code. -/
example :
    wordSsaRenameMove (α := Nat)
        ({ current := [], next := 200 } : WordSsaState) 0 [(15, 4), (16, 12)] =
      ({ current := [(12, 204), (4, 200), (16, 204), (15, 200)], next := 208 },
        (.move 0 [(200, 4), (204, 12)] : WordProg Nat)) := by
  simp [wordSsaRenameMove, wordSsaFreshList, wordSsaFresh, wordSsaRead,
    wordSsaForceRename, lookupNatInfo]

end Flapjack
