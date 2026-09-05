import Flapjack.Pipeline

namespace Flapjack

example :
    wordAllocateContext [0, 1, 29, 30] =
      some { vars := [(0, 2), (1, 3), (29, 4), (30, 5)] } := by
  exact wordAllocateContext_examples

example :
    wordAllocateContext [0, 1, 2, 3] =
      some { vars := [(0, 2), (1, 3), (2, 4), (3, 5)] } := by
  exact wordAllocateContext_preserves_small_names

example :
    wordAllocateContextWithClashes [0, 1, 28]
        [(0, 1), (1, 28)] =
      some { vars := [(28, 2), (1, 3), (0, 2)] } := by
  exact wordAllocateContextWithClashes_examples

example :
    wordAllocateVarsWithClashes [0, 1] [(0, 1)] =
      some [(1, 3), (0, 2)] := by
  exact wordAllocateVarsWithClashes_safe_example

example :
    wordInstVars (.arith (.addCarry 1 2 3 4 5)) = [3, 4, 5, 1, 2] := by
  exact wordInstVars_addCarry

example :
    wordAllocateLinearInstructions
      [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      some { vars := [(6, 8), (5, 7), (1, 3), (0, 2), (4, 6), (3, 5), (2, 4)] } := by
  exact wordAllocateLinearInstructions_example

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
    wordProgClashAnalysis
        ((.seq (.assign 0 (.var 1)) (.assign 2 (.var 0))) : WordProg α) [] =
      ([1], []) := by
  exact wordProgClashAnalysis_seq

example :
    wordProgClashAnalysis
        ((.ite .equal 0 (.reg 1)
          (.assign 2 (.var 0)) (.assign 3 (.var 0))) : WordProg α) [] =
      ([0, 1], []) := by
  exact wordProgClashAnalysis_ite

example :
    (wordAllocateSsaProgram
      ({ current := [], next := 10 } : WordSsaState)
      ((.ite .equal 0 (.reg 0)
        (.assign 1 (.var 0)) (.assign 1 (.var 0))) : WordProg Nat)).isSome =
      true := by
  native_decide

example (slots : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  exact wordAllocateVarsWithClashes_sound slots edges colouring hcolouring

example [OfNat α 1] :
    pipelineWordFunctionsAllocated
      ([] : List (Nat × List Nat × LoopProg α)) = some [] := by
  rfl

example [OfNat α 1] :
    pipelineWordFunctionsAllocatedWithAnalysis
      [(0, [0], (.assign 1 (.var 0) : LoopProg α))] =
      some [(0, [2], (.assign 3 (.var 2) : WordProg α))] := by
  simp [pipelineWordFunctionsAllocatedWithAnalysis,
    wordAllocateProgramWithSlots, wordAllocateContextWithClashes,
    wordAllocateVarsWithClashes, wordGreedyColour, wordColourCandidates,
    wordFirstAvailable, wordPreferredRegister,
    wordAllocatableRegisters, wordNeighbours, wordUsedRegisters,
    wordRegisterIsAllocatable,
    wordColouringUsesAllocatable, wordColouringRespectsClashes,
    wordProgClashAnalysis, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs,
    wordExpReadVars, loopAccVars, loopVarsOfExp, loopInsertAll, loopInsert,
    loopToWordProg, wordCompileExp, wordFindVar, wordMapVars, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example [OfNat α 1] :
    pipelineWordFunctionsAllocatedWithAnalysisAndColour
      [(0, [0], (.assign 1 (.var 0) : LoopProg α))] =
      some [(0, [2], (.assign 3 (.var 2) : WordProg α))] := by
  simp [pipelineWordFunctionsAllocatedWithAnalysisAndColour,
    wordAllocateProgramWithSlotsAndColour, wordAllocateContextWithClashes,
    wordAllocateVarsWithClashes, wordGreedyColour, wordColourCandidates,
    wordFirstAvailable, wordPreferredRegister, wordAllocatableRegisters,
    wordNeighbours, wordUsedRegisters, wordRegisterIsAllocatable,
    wordColouringUsesAllocatable, wordColouringRespectsClashes,
    wordProgClashAnalysis, wordProgVariables, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordExpReadVars, loopAccVars, loopVarsOfExp,
    loopInsertAll, loopInsert, loopToWordProg, wordCompileExp, wordFindVar,
    wordApplyColour, wordApplyColourExp, wordMapVars, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.shareInst .load 1
          (.op .add [.var 2, .const (4 : Nat)])) : WordProg Nat) =
        ({ current := [(1, 200), (2, 100)], next := 201 },
        .shareInst .load 200 (.op .add [.var 100, .const 4])) := by
  simp [wordSsaRenameProgram, wordSsaRenameExp, wordSsaFresh,
    wordSsaRead, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.call (some ([3, 4], [2])) (some 7) [2, 5] none) : WordProg Nat) =
        ({ current := [(4, 201), (3, 200), (2, 100)], next := 202 },
        .call (some ([200, 201], [100])) (some 7) [100, 5] none) := by
  simp [wordSsaRenameProgram, wordSsaRenameReturns, wordSsaFreshList,
    wordSsaFresh, wordSsaRead, lookupNatInfo]

example :
    wordSsaRenameProgram
        ({ current := [(2, 100)], next := 200 } : WordSsaState)
        ((.seq (.locValue 3 2) (.return 0 [3])) : WordProg Nat) =
      ({ current := [(3, 200), (2, 100)], next := 201 },
        .seq (.locValue 200 100) (.return 0 [200])) := by
  rfl

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

end Flapjack
