import Flapjack.Pipeline

namespace Flapjack

def pipelineAllocatedMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := true, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 6), .const (BitVec.ofNat 64 7)]),
      returnShape := .one }]

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

example [NeZero width] :
    pipelineWordFunctionsAllocatedWithSpills
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word width))) = some [] := by
  rfl

example :
    (pipelineWordFunctionsAllocatedWithSpills
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome := by
  native_decide

example :
    (compileFlapjackRiscVViaAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).isSome := by
  native_decide

end Flapjack
