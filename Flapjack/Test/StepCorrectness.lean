import Flapjack.RiscV.StepCorrectness

/-! Regression coverage for the exact RISC-V instruction-step contracts. -/

namespace Flapjack.RiscV

def noFfiHost : WordFfiHost 8 := fun _ _ _ _ _ _ => none

def advancingFfiHost : WordFfiHost 8 :=
  fun _ _ _ _ _ state => some { state with pc := state.pc + 4 }

def stepCountState : State 8 :=
  writeRegister (zeroState 8) 1 7

def stepCountProgram : WordProg (Word 8) :=
  .seq (.assign 2 (.var 1)) (.return 0 [2])

example :
    executeInstructionsCounted stepCountState [.addi 2 1 0] =
      (executeInstructions stepCountState [.addi 2 1 0], 1) := by
  simpa using executeInstructionsCounted_spec stepCountState [.addi 2 1 0]

example :
    wordProgToRiscV (.assign 2 (.var 1) : WordProg (Word 8)) =
      some [.addi 2 1 0] := by
  simp [wordProgToRiscV, wordExpToInstructions, wordExpToInstruction,
    registerOfNat]

example :
    some (executeInstructionsCounted stepCountState [.addi 2 1 0]) =
      (evalWordProg stepCountState
        (.assign 2 (.var 1) : WordProg (Word 8))).map
        (fun final => (final, 1)) := by
  apply wordProgToRiscV_counted_sound_of_straightLine
    stepCountState (.assign 2 (.var 1))
  · exact .assign 2 (.var 1)
  · simp [wordProgToRiscV, wordExpToInstructions, wordExpToInstruction,
      registerOfNat]

example (host : WordFfiHost 8) (state : State 8) :
    executeInstructionsWithFfiCounted host state [] = some (state, 0) := by
  rfl

example (host : WordFfiHost 8) (state : State 8) :
    executeInstructionsWithFfi host state [.addi 1 0 1] =
      some (executeInstructions state [.addi 1 0 1]) := by
  apply executeInstructionsWithFfi_of_ne_ecall
  intro instruction hinstruction
  simp at hinstruction
  subst instruction
  simp

example (host : WordFfiHost 8) (state : State 8) :
    executeInstructionsWithFfiCounted host state [.addi 1 0 1] =
      some (executeInstructions state [.addi 1 0 1], 1) := by
  apply executeInstructionsWithFfiCounted_of_ne_ecall
  · intro instruction hinstruction
    simp at hinstruction
    subst instruction
    simp
  · rfl

example (host : WordFfiHost 8) (fuel : Nat) (start returnAddress : Word 8)
    (code : List (Instruction 8)) (state : State 8) :
    (executeCodeUntilWithFfiCounted host fuel start returnAddress code state).map
        Prod.fst =
      executeCodeUntilWithFfi host fuel start returnAddress code state := by
  exact executeCodeUntilWithFfiCounted_fst host fuel start returnAddress code state

example (host : WordFfiHost 8) (fuel : Nat) (start returnAddress : Word 8)
    (code : List (Instruction 8)) (state final : State 8) (count : Nat)
    (hcount :
      executeCodeUntilWithFfiCounted host fuel start returnAddress code state =
        some (final, count)) :
    count ≤ fuel := by
  exact executeCodeUntilWithFfiCounted_count_le_fuel host fuel start returnAddress
    code state final count hcount

example :
    executeCodeUntilWithFfiCounted noFfiHost
        2 0 (4#8) [.addi 2 1 0] (zeroState 8) =
      executeInstructionsWithFfiCounted noFfiHost
        (zeroState 8) [.addi 2 1 0] := by
  apply executeCodeUntilWithFfiCounted_suffix
    (host := noFfiHost)
    (state := zeroState 8) (prelude := []) (suffix := [.addi 2 1 0])
    (tail := [])
  · rfl
  · intro current instruction hmem next hstep
    have hinstruction : instruction = .addi 2 1 0 := by simpa using hmem
    subst instruction
    simp [executeWithFfi, execute, nextPc] at hstep
    simpa [writeRegister] using (congrArg State.pc hstep).symm
  · decide

example :
    executeCodeUntilWithFfiCounted advancingFfiHost
        2 0 (4#8) [.ecall] (zeroState 8) =
      executeInstructionsWithFfiCounted advancingFfiHost
        (zeroState 8) [.ecall] := by
  apply executeCodeUntilWithFfiCounted_suffix
    (host := advancingFfiHost)
    (state := zeroState 8) (prelude := []) (suffix := [.ecall]) (tail := [])
  · rfl
  · intro current instruction hmem next hstep
    have hinstruction : instruction = .ecall := by simpa using hmem
    subst instruction
    simp [executeWithFfi, advancingFfiHost] at hstep
    simpa [advancingFfiHost] using (congrArg State.pc hstep).symm
  · decide

example (context : WordCallContext 8) (state : State 8)
    (code : List (Instruction 8))
    (hcompile : wordFunctionToRiscVWithCalls context
      (.assign 2 (.var 1) : WordProg (Word 8)) = some (code, [])) :
    evalWordFunction state (.assign 2 (.var 1) : WordProg (Word 8)) =
      some ((executeInstructionsCounted state code).1, []) := by
  apply wordFunctionToRiscV_counted_sound_of_straightLine
    context state (.assign 2 (.var 1))
  · exact .assign 2 (.var 1)
  · exact hcompile

example (state : State 8) (entry : Word 8) (moves : List (Instruction 8))
    (hzero : ZeroRegister state) :
    (executeInstructions state
      (moves ++ [.addi 31 0 entry, .jalr 0 31 0])).pc =
      jalrTarget entry 0 := by
  exact executeInstructions_tailCall_pc state entry moves hzero

example (state : State 8) (entry : Word 8) (parameters arguments : List Nat)
    (code : List (Instruction 8)) (hzero : ZeroRegister state)
    (hcompile : wordTailCallToRiscV entry parameters arguments = some code) :
    (executeInstructions state code).pc = jalrTarget entry 0 := by
  exact wordTailCallToRiscV_execute_pc state entry parameters arguments code
    hzero hcompile

example (state : State 8) (entry : Word 8) (code : List (Instruction 8))
    (hzero : ZeroRegister state)
    (hcompile : wordTailCallToRiscV entry [2] [3] = some code) :
    readRegister (executeInstructions state code) 2 = readRegister state 3 ∧
      (executeInstructions state code).pc = jalrTarget entry 0 := by
  exact wordTailCallToRiscV_execute_single_parameter state entry 2 3 code hzero
    (by decide) (by decide) (by decide) (by decide) hcompile

example (state : State 8) (entry : Word 8) (code : List (Instruction 8))
    (hzero : ZeroRegister state)
    (hcompile : wordTailCallToRiscV entry [2, 3] [4, 5] = some code) :
    readRegister (executeInstructions state code) 2 = readRegister state 4 ∧
      readRegister (executeInstructions state code) 3 = readRegister state 5 ∧
      (executeInstructions state code).pc = jalrTarget entry 0 := by
  have htransfer := wordTailCallToRiscV_execute_moves_transfer state entry
    [2, 3] [4, 5] code hzero
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by decide)
    (by
      intro move hmove
      simp at hmove ⊢
      rcases hmove with rfl | rfl <;> decide)
    hcompile
  have hfirst := htransfer.1 (2, 4) (by simp)
  have hsecond := htransfer.1 (3, 5) (by simp)
  exact ⟨by simpa using hfirst, by simpa using hsecond, htransfer.2⟩

example (state : State 8) (entry : Word 8) (moves : List (Instruction 8))
    (hzero : ZeroRegister state) :
    (executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
      jalrTarget entry 0 := by
  exact executeInstructions_stackCall_pc state entry moves hzero

example (state : State 8) (entry : Word 8) (moves : List (Instruction 8)) :
    readRegister (executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])) 2 =
      readRegister (executeInstructions state moves) 2 := by
  exact executeInstructions_stackCall_read_register state entry moves 2
    (by decide) (by decide) (by decide)

example (state : State 8) (entry : Word 8) (moves : List (Instruction 8))
    (hzero : ZeroRegister state) :
    let moved := executeInstructions state moves
    let final := executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])
    readRegister final 1 = moved.pc + BitVec.ofNat 8 16 ∧
      readRegister final 30 =
        readRegister moved 30 - BitVec.ofNat 8 (8 / 8) ∧
      final.pc = jalrTarget entry 0 := by
  exact executeInstructions_stackCall_prologue_effects state entry moves hzero

example (state : State 8) (entry : Word 8)
    (parameters returns arguments destinations : List Nat)
    (code : List (Instruction 8)) (hzero : ZeroRegister state)
    (hcompile :
      wordCallToRiscVWithStack entry parameters returns arguments destinations =
        some code) :
    ∃ parameterMoves resultMoves,
      (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
        jalrTarget entry 0 ∧
      code =
        parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves := by
  exact wordCallToRiscVWithStack_prefix_execute_pc state entry parameters returns
    arguments destinations code hzero hcompile

example (state : State 8) (entry : Word 8) (code : List (Instruction 8))
    (hzero : ZeroRegister state)
    (hcompile : wordCallToRiscVWithStack entry [2, 3] [6] [4, 5] [7] =
      some code) :
    ∃ parameterMoves resultMoves,
      wordRegisterMoves (width := 8)
        ([2, 3].zip [4, 5] : List (Nat × Nat)) =
        some parameterMoves ∧
      readRegister (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])) 2 =
        readRegister state 4 ∧
      readRegister (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])) 3 =
        readRegister state 5 ∧
      (executeInstructions state
        (parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
        jalrTarget entry 0 ∧
      code = parameterMoves ++
        [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++ resultMoves := by
  have hresult := wordCallToRiscVWithStack_prefix_execute_parameter_transfer state entry
    [2, 3] [6] [4, 5] [7] code hzero
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by decide)
    (by
      intro move hmove
      simp at hmove ⊢
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    hcompile
  rcases hresult with ⟨parameterMoves, resultMoves, hmoves, htransfer, hpc, hcode⟩
  refine ⟨parameterMoves, resultMoves, hmoves, ?_, ?_, hpc, hcode⟩
  · simpa using htransfer (2, 4) (by simp)
  · simpa using htransfer (3, 5) (by simp)

example (state : State 8) (stackAddress savedLink : Word 8)
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink) :
    let final := executeInstructions state
      [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))]
    readRegister final 1 = savedLink ∧
      readRegister final 30 = stackAddress + BitVec.ofNat 8 (8 / 8) ∧
      final.pc = state.pc + BitVec.ofNat 8 8 := by
  exact executeInstructions_stackCall_restore_link_sp state stackAddress savedLink
    hstack hsaved

example (state : State 8) (stackAddress savedLink : Word 8)
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink) :
    let moved := executeInstructions state
      (([(2, 4)] : List (Nat × Nat)).flatMap
        (wordMoveInstructionList (width := 8)))
    let final := executeInstructions state
      (([(2, 4)] : List (Nat × Nat)).flatMap
        (wordMoveInstructionList (width := 8)) ++
        [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])
    readRegister final 1 = savedLink ∧
      readRegister final 30 =
        stackAddress + BitVec.ofNat 8 (8 / 8) ∧
      final.pc = moved.pc + BitVec.ofNat 8 8 := by
  exact executeWordMoves_stackCall_restore_link_sp state stackAddress savedLink
    [(2, 4)]
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    hstack hsaved

example (state : State 8) (stackAddress savedLink : Word 8)
    (code : List (Instruction 8))
    (hstack : readRegister state 30 = stackAddress)
    (hsaved : readWordValue state stackAddress = savedLink)
    (hcompile : wordRegisterMoves (width := 8) [(2, 6)] = some code) :
    let final := executeInstructions state
      (code ++ [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])
    readRegister final 1 = savedLink ∧
      readRegister final 30 =
        stackAddress + BitVec.ofNat 8 (8 / 8) ∧
      final.pc = (executeInstructions state code).pc + BitVec.ofNat 8 8 := by
  exact wordRegisterMoves_execute_stackCall_restore_link_sp state stackAddress
    savedLink [(2, 6)] code
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    hstack hsaved hcompile

example (returnState : State 8) (stackAddress savedLink entry : Word 8)
    (code : List (Instruction 8))
    (hstack : readRegister returnState 30 = stackAddress)
    (hsaved : readWordValue returnState stackAddress = savedLink)
    (hcompile : wordCallToRiscVWithStack entry [2] [6] [4] [7] = some code) :
    ∃ parameterMoves resultMoves,
      code = parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))] ∧
      let final := executeInstructions returnState
        (resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])
      readRegister final 1 = savedLink ∧
        readRegister final 30 =
          stackAddress + BitVec.ofNat 8 (8 / 8) ∧
        final.pc = (executeInstructions returnState resultMoves).pc +
          BitVec.ofNat 8 8 := by
  exact wordCallToRiscVWithStack_full_return_contract returnState stackAddress
    savedLink entry [2] [6] [4] [7] code
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl
      decide)
    hstack hsaved hcompile

example (state : State 8) (code : List (Instruction 8))
    (hcompile : wordRegisterMoves (width := 8) [(2, 6), (3, 7)] = some code) :
    readRegister (executeInstructions state
      (code ++ [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])) 2 =
        readRegister state 6 ∧
      readRegister (executeInstructions state
        (code ++ [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])) 3 =
        readRegister state 7 := by
  have htransfer := wordRegisterMoves_execute_stackCall_result_transfer state
    [(2, 6), (3, 7)] code
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove ⊢
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    hcompile
  exact ⟨by simpa using htransfer (2, 6) (by simp),
    by simpa using htransfer (3, 7) (by simp)⟩

example (state : State 8) (entry : Word 8) (code : List (Instruction 8))
    (hcompile : wordCallToRiscVWithStack entry [8, 9] [6, 7] [4, 5] [2, 3] =
      some code) :
    ∃ parameterMoves resultMoves,
      code = parameterMoves ++
          [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
           .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0] ++
          resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))] ∧
      readRegister (executeInstructions state
        (resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])) 2 =
        readRegister state 6 ∧
      readRegister (executeInstructions state
        (resultMoves ++
          [.loadWord 1 30, .addi 30 30 (BitVec.ofNat 8 (8 / 8))])) 3 =
        readRegister state 7 := by
  have hresult := wordCallToRiscVWithStack_full_result_contract state entry
    [8, 9] [6, 7] [4, 5] [2, 3] code
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    (by
      intro move hmove
      simp at hmove
      rcases hmove with rfl | rfl <;> decide)
    hcompile
  rcases hresult with ⟨parameterMoves, resultMoves, hcode, htransfer⟩
  refine ⟨parameterMoves, resultMoves, hcode, ?_, ?_⟩
  · simpa using htransfer (2, 6) (by simp)
  · simpa using htransfer (3, 7) (by simp)

example (state : State 8) (code : List (Instruction 8))
    (hcode : ∀ instruction ∈ code, instruction.isBranch = false) :
    (executeInstructions state code).pc =
      code.foldl (fun pc _ => pc + 4) state.pc := by
  exact executeInstructions_pc_fold_of_nonbranching state code hcode

example (state : State 8) (code : List (Instruction 8))
    (hcode : ∀ instruction ∈ code, instruction.isBranch = false) :
    (executeInstructions state code).pc =
      state.pc + BitVec.ofNat 8 (code.length * 4) := by
  exact executeInstructions_pc_of_nonbranching state code hcode

example :
    executeCode 3 0 [.addi 1 0 7, .addi 2 1 3] (zeroState 8) =
      some (executeInstructions (zeroState 8) [.addi 1 0 7, .addi 2 1 3]) := by
  simpa using (executeCode_of_nonbranching (zeroState 8)
    ([.addi 1 0 7, .addi 2 1 3] : List (Instruction 8)) (by rfl) (by
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | rfl | hfalse
      · rfl
      · rfl
      · contradiction) (by decide))

example :
    executeCodeUntil 3 0 (BitVec.ofNat 8 12)
        ([.branchEq 0 0 0, .addi 1 0 7, .addi 2 1 3, .addi 3 2 1])
        ({zeroState 8 with pc := BitVec.ofNat 8 4}) =
      some (executeInstructions ({zeroState 8 with pc := BitVec.ofNat 8 4})
        [.addi 1 0 7, .addi 2 1 3]) := by
  simpa using (executeCodeUntil_suffix_of_nonbranching
    ({zeroState 8 with pc := BitVec.ofNat 8 4})
    ([.branchEq 0 0 0] : List (Instruction 8))
    [.addi 1 0 7, .addi 2 1 3]
    [.addi 3 2 1] (by rfl) (by
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | rfl | hfalse
      · rfl
      · rfl
      · contradiction) (by decide))

example :
    executeCodeUntil 5 0 (BitVec.ofNat 8 12)
        ([.branchEq 0 0 0, .addi 1 0 7, .addi 2 1 3, .addi 3 2 1])
        ({zeroState 8 with pc := BitVec.ofNat 8 4}) =
      some (executeInstructions ({zeroState 8 with pc := BitVec.ofNat 8 4})
        [.addi 1 0 7, .addi 2 1 3]) := by
  simpa using (executeCodeUntil_suffix_of_nonbranching_fuel
    ({zeroState 8 with pc := BitVec.ofNat 8 4})
    ([.branchEq 0 0 0] : List (Instruction 8))
    [.addi 1 0 7, .addi 2 1 3]
    [.addi 3 2 1] 2 (by rfl) (by
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | rfl | hfalse
      · rfl
      · rfl
      · contradiction) (by decide))

end Flapjack.RiscV
