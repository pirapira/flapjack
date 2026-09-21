import Flapjack.Pipeline

namespace Flapjack

def pipelineAllocatedMulDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "mul", inline := false, exported := true, params := [],
      body := .return (.panOp .mul
        [.const (BitVec.ofNat 64 6), .const (BitVec.ofNat 64 7)]),
      returnShape := .one }]

/- The production allocator uses the difference-list inventory only at its
   measured hot spots.  This mixed fixture covers the Cake preorder through a
   sequence, loop, call return cutsets, and handler body. -/
def allocatorReadVarsFastFixture : WordProg Nat :=
  .seq (.assign 3 (.var 2))
    (.seq (.loop [4] (.assign 5 (.var 6)) [7])
      (.call (some ([8], ([9], [10]), .assign 11 (.var 12), 13, 14))
        (some 15) [16]
        (some (17, .assign 18 (.var 19), 20, 21))))

example :
    wordProgReadVarsFast allocatorReadVarsFastFixture =
      wordProgReadVars allocatorReadVarsFastFixture := by
  simp [wordProgReadVarsFast, wordProgReadVarsFastAcc, wordListAppendAcc,
    wordExpReadVarsFastAcc, wordProgReadVars,
    wordExpReadVars, allocatorReadVarsFastFixture]

example :
    wordInstReadVarsFastAcc
        (.arith (.longDiv 1 2 3 4 5) : WordInst Nat) [6, 7] =
      [3, 4, 5, 6, 7] := by
  rfl

example :
    wordInstWriteVarsFastAcc
        (.memOffset .store 8 9 10 : WordInst Nat) [11] =
      [11] := by
  rfl

example :
    wordProgLiveBeforeFast allocatorReadVarsFastFixture [22, 23] =
      wordProgLiveBefore allocatorReadVarsFastFixture [22, 23] := by
  simp [wordProgLiveBeforeFast, wordProgLiveBefore,
    wordProgReadVarsFastAcc, wordListAppendAcc, wordExpReadVarsFastAcc,
    wordProgReadVars, wordProgWriteVarsFast, wordProgWriteVarsFastAcc,
    wordProgWriteVars, wordExpReadVars,
    allocatorReadVarsFastFixture]

def allocatorWriteVarsFastFixture : WordProg Nat :=
  .seq
    (.call (some ([31], ([], [32]),
      .seq (.assign 33 (.var 34)) (.locValue 35 0), 7, 8))
      (some 9) [10, 11]
      (some (12, .seq (.assign 36 (.var 37)) (.get 38 .currHeap), 9, 10)))
    (.ite .equal 39 (.reg 40)
      (.assign 41 (.var 42))
      (.seq (.alloc 43 ([], [])) (.shareInst .load 44 (.var 45))))

example :
    wordProgWriteVarsFast allocatorWriteVarsFastFixture =
      wordProgWriteVars allocatorWriteVarsFastFixture := by
  simp [wordProgWriteVarsFast, wordProgWriteVarsFastAcc, wordProgWriteVars,
    wordListAppendAcc, allocatorWriteVarsFastFixture]

example :
    wordProgLiveBeforeFast allocatorWriteVarsFastFixture [41, 43, 44] =
      wordProgLiveBefore allocatorWriteVarsFastFixture [41, 43, 44] := by
  simp [wordProgLiveBeforeFast, wordProgLiveBefore,
    wordProgReadVarsFastAcc, wordProgWriteVarsFast, wordProgWriteVarsFastAcc,
    wordListAppendAcc, wordExpReadVarsFastAcc, wordProgReadVars,
    wordProgWriteVars, wordExpReadVars, allocatorWriteVarsFastFixture]

example :
    wordProgAtomicClashesFast allocatorWriteVarsFastFixture [46, 47] =
      wordProgAtomicClashes allocatorWriteVarsFastFixture [46, 47] := by
  simp [wordProgAtomicClashesFast, wordProgAtomicClashes,
    wordProgWriteVarsFast, wordProgWriteVarsFastAcc, wordProgWriteVars,
    wordClashPairs, wordClashPairsFast, wordClashPairsFastAcc,
    wordListAppendAcc,
    allocatorWriteVarsFastFixture]

example :
    wordProgAtomicClashesFast
        (.inst (.arith (.div 48 49 50)) : WordProg Nat) [51] =
      wordProgAtomicClashes
        (.inst (.arith (.div 48 49 50)) : WordProg Nat) [51] := by
  simp [wordProgAtomicClashesFast, wordProgAtomicClashes,
    wordProgWriteVarsFast, wordProgWriteVarsFastAcc, wordProgWriteVars,
    wordClashPairs, wordClashPairsFast, wordClashPairsFastAcc,
    wordInstForcedClashes, wordInstWriteVars,
    wordInstWriteVarsFastAcc]

example :
    wordClashPairsFast [4, 5] [4, 6, 5, 7] =
      wordClashPairs [4, 5] [4, 6, 5, 7] := by
  rfl

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
    wordProgClashAnalysis, wordProgVariablesFast,
    wordProgLiveBeforeFast, wordProgReadVarsFastAcc,
    wordProgWriteVarsFast, wordProgWriteVarsFastAcc,
    wordProgAtomicClashesFast, wordClashPairsFast, wordClashPairsFastAcc,
    wordExpReadVarsFastAcc, loopAccVars, loopInsert,
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
    wordProgClashAnalysis, wordProgVariablesFast,
    wordProgLiveBeforeFast, wordProgReadVarsFastAcc,
    wordProgWriteVarsFast, wordProgWriteVarsFastAcc,
    wordProgAtomicClashesFast, wordClashPairsFast, wordClashPairsFastAcc,
    wordExpReadVarsFastAcc, loopAccVars, loopInsert,
    loopToWordProg, wordCompileExp, wordFindVar,
    wordApplyColour, wordApplyColourExp, wordMapVars, lookupNatInfo,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

example [NeZero width] :
    pipelineWordFunctionsAllocatedWithSpills
      ([] : List (Nat × List Nat × LoopProg (RiscV.Word width))) = some [] := by
  rfl

#guard
    (pipelineWordFunctionsAllocatedWithGraph
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome

#guard
    (wordAllocateGraphFunctionWithStackOnlyPrefreezeRenamed [2]
      (.assign 3 (.var 2) : WordProg (RiscV.Word 64)) [] 13 14).isSome

/- Cake's `word_to_stack` emits no parameter prelude: the incoming ABI
   registers are copied by the SSA entry move, so a function with no body
   lowers to that body alone. -/
example :
    RiscV.wordToStackFunctionWithParameters
        { locations := [(0, .stack 0)], scratch := 31, stackBase := 10 }
        [0]
        ((.skip : WordProg (RiscV.Word 64))) =
      some (.skip : StackProg Nat) := by
  simp [RiscV.wordToStackFunctionWithParameters, RiscV.wordToStackProgWord,
    RiscV.wordToStackProgNat, RiscV.wordProgToNat]

#guard
    (pipelineWordFunctionsAllocatedWithSpills
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).isSome


#guard
    (pipelineWordFunctionsAllocatedWithSpills
      [(0, [0], (.assign 1 (.var 0) : LoopProg (RiscV.Word 64))) ]).map
        (fun functions => functions.map (fun (_, parameters, _) => parameters)) =
      some [[2]]

#guard
    (compileFlapjackRiscVViaAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).isSome

#guard
    (compileFlapjackRiscVViaGraphAllocatedStack (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).isSome

#guard
    (compileFlapjackRiscVViaGraphAllocatedStackLinked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      { storeBase := 10, currHeap := 12, scratch := 31,
        addressScratch := 29, stackPointer := 20, bytesInWord := 8,
        stackBase := 21, wordShift := 3 }
      pipelineAllocatedMulDeclarations).map
        (fun sections => sections.map (fun (label, entry, _) => (label, entry))) =
      some [(0, BitVec.ofNat 64 0), (1, BitVec.ofNat 64 40)]

/-- A `Get` writes its destination, so the write-variable walk must report it.
    Cake's `vars_of`/`max_var` include `Get` destinations, and the spill
    allocator and condition folder rely on the same classification here. -/
example : wordProgWriteVars (.get 5 .currHeap : WordProg Nat) = [5] := rfl

/- Cake's full SSA AddCarry protocol uses fixed register 0 for the carry
   flag and refreshes the source carry after the instruction. -/
example :
    (wordSsaRenameProgramWithLoops []
      { current := [(1, 10), (2, 20), (3, 30), (4, 40)], next := 44 }
      (.inst (.arith (.cakeAddCarry 3 2 4 1)) : WordProg Nat)).2 =
      (.seq (.move 1 [(0, 10)])
        (.seq (.inst (.arith (.cakeAddCarry 44 20 40 0)))
          (.move 1 [(48, 0)])) : WordProg Nat) := by
  simp [wordSsaRenameProgramWithLoops, wordSsaRead, wordSsaFresh, wordSsaSeq,
    lookupNatInfo]

/- The carry refresh must update the original carry key, not the already-read
   SSA value.  This is observable by the assignment immediately following the
   fixed-register AddCarry protocol and is the Cake `ssa_cc_trans_inst`
   source-shaped continuation. -/
example :
    (wordSsaRenameProgramWithLoops []
      { current := [(1, 10), (2, 20), (3, 30), (4, 40)], next := 44 }
      (.seq (.inst (.arith (.cakeAddCarry 3 2 4 1)))
        (.assign 4 (.var 1)) : WordProg Nat)).2 =
      (.seq
        (.seq (.move 1 [(0, 10)])
          (.seq (.inst (.arith (.cakeAddCarry 44 20 40 0)))
            (.move 1 [(48, 0)])))
        (.assign 52 (.var 48)) : WordProg Nat) := by
  simp [wordSsaRenameProgramWithLoops, wordSsaRead, wordSsaFresh, wordSsaSeq,
    wordSsaRenameExp, lookupNatInfo]

end Flapjack
