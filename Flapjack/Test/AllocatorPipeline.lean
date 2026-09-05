import Flapjack.Pipeline

namespace Flapjack

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

end Flapjack
