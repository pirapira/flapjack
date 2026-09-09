import Flapjack.RiscV.StepCorrectness

/-! Regression coverage for the exact RISC-V instruction-step contracts. -/

namespace Flapjack.RiscV

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

example (state : State 8) (entry : Word 8) (moves : List (Instruction 8))
    (hzero : ZeroRegister state) :
    (executeInstructions state
      (moves ++
        [.addi 30 30 (0 - BitVec.ofNat 8 (8 / 8)),
         .storeWord 1 30, .addi 31 0 entry, .jalr 1 31 0])).pc =
      jalrTarget entry 0 := by
  exact executeInstructions_stackCall_pc state entry moves hzero

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

end Flapjack.RiscV
