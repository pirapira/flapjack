import Flapjack.RiscV.CorrectnessConditional

namespace Flapjack.Test.CorrectnessConditional

open Flapjack Flapjack.RiscV

def testNoFfiHost : WordFfiHost 8 := fun _ _ _ _ _ _ => none

example (state : State 64) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction 64)
    (hpc : state.pc = 0)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat 64 8)
        , elseInstruction ] state |>.isSome := by
  rw [executeCode_conditional_single state operator left right thenInstruction
    elseInstruction hpc (by decide) hthen helse]
  split <;> simp

example (state : State 32) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction 32)
    (hpc : state.pc = 0)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat 32 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat 32 8)
        , elseInstruction ] state |>.isSome := by
  rw [executeCode_conditional_single state operator left right thenInstruction
    elseInstruction hpc (by decide) hthen helse]
  split <;> simp

example :
    executeCodeUntilWithFfiCounted testNoFfiHost 3 0 (8#8)
        ([.addi 1 0 7] : List (Instruction 8)) (zeroState 8) =
      (executeInstructionsWithFfiCounted testNoFfiHost (zeroState 8)
        [.addi 1 0 7]).bind
        (fun result =>
          (executeCodeUntilWithFfiCounted testNoFfiHost 2 0 (8#8)
            [.addi 1 0 7] result.1).map
            (fun final => (final.1, final.2 + 1))) := by
  apply executeCodeUntilWithFfiCounted_after_nonbranching
    (host := testNoFfiHost) (state := zeroState 8)
    (prelude := []) (suffix := [.addi 1 0 7]) (tail := [])
    (fuel := 2) (returnAddress := (8#8))
  · rfl
  · intro current instruction hinstruction next hstep
    have hinstruction' : instruction = .addi 1 0 7 := by
      simpa using hinstruction
    subst instruction
    simp [executeWithFfi, execute, nextPc] at hstep
    simpa [executeWithFfi, execute, writeRegister, nextPc] using
      (congrArg State.pc hstep).symm
  · decide
  · decide

example (state final : State 8)
    (hfinal :
      executeInstructionsWithFfi testNoFfiHost state [.addi 1 0 7] =
        some final) :
    final.pc = state.pc + BitVec.ofNat 8 4 := by
  apply executeInstructionsWithFfi_pc_of_advance
    (host := testNoFfiHost) (state := state)
    (instructions := [.addi 1 0 7])
  · intro current instruction hinstruction next hstep
    have hinstruction' : instruction = .addi 1 0 7 := by
      simpa using hinstruction
    subst instruction
    simp [executeWithFfi, execute, writeRegister, nextPc] at hstep
    simpa [executeWithFfi, execute, writeRegister, nextPc] using
      (congrArg State.pc hstep).symm
  · exact hfinal

example (state final : State 8) (count : Nat)
    (hfinal :
      executeInstructionsWithFfiCounted testNoFfiHost state [.addi 1 0 7] =
        some (final, count)) :
    final.pc = state.pc + BitVec.ofNat 8 4 := by
  apply executeInstructionsWithFfiCounted_pc_of_advance
    (host := testNoFfiHost) (state := state)
    (instructions := [.addi 1 0 7])
  · intro current instruction hinstruction next hstep
    have hinstruction' : instruction = .addi 1 0 7 := by
      simpa using hinstruction
    subst instruction
    simp [executeWithFfi, execute, writeRegister, nextPc] at hstep
    simpa [executeWithFfi, execute, writeRegister, nextPc] using
      (congrArg State.pc hstep).symm
  · exact hfinal

example :
    wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word 64)))
          (.assign 3 (.const (2 : Word 64)))) : WordProg (Word 64)) =
      some ([.branchNe 1 2 (BitVec.ofNat 64 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 64 8), .addi 3 0 2], []) := by
  exact wordFunctionToRiscV_ite_assign

example :
    wordFunctionToRiscVWithCalls (⟨[]⟩ : WordCallContext 8)
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word 8)))
          (.assign 3 (.const (2 : Word 8)))) : WordProg (Word 8)) =
      some ([.branchNe 1 2 (BitVec.ofNat 8 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 8 8), .addi 3 0 2], []) := by
  apply wordFunctionToRiscVWithCalls_ite_shape
    (context := (⟨[]⟩ : WordCallContext 8))
    (operator := .equal) (condition := 1) (rightValue := .reg 2)
    (thenBranch := (.assign 3 (.const (1 : Word 8))))
    (elseBranch := (.assign 3 (.const (2 : Word 8))))
    (branchLeft := 1) (right := 2) (prelude := [])
    (thenCode := [.addi 3 0 1]) (elseCode := [.addi 3 0 2])
    (thenReturns := []) (elseReturns := [])
  · simp [wordConditionOperands, registerOfNat]
  · simp [wordFunctionToRiscVWithCalls, wordExpToInstructions,
      wordExpToInstruction, registerOfNat]
  · simp [wordFunctionToRiscVWithCalls, wordExpToInstructions,
      wordExpToInstruction, registerOfNat]
  · rfl

example (state : State 8) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    ∃ sourceState machineState,
      evalWordFunction state
          ((.ite .equal 1 (.reg 2) .skip .skip) : WordProg (Word 8)) =
        some (sourceState, []) ∧
      executeCodeUntil 3 0 (BitVec.ofNat 8 8)
          [.branchNe 1 2 (BitVec.ofNat 8 8),
            .branchEq 0 0 (BitVec.ofNat 8 4)] state = some machineState ∧
      StateDataRelation sourceState machineState := by
  apply evalWordFunction_ite_executeCodeUntil_of_nonbranching
    (state := state) (operator := .equal) (condition := 1) (source := 2)
    (thenBranch := (.skip : WordProg (Word 8)))
    (elseBranch := (.skip : WordProg (Word 8)))
    (branchLeft := 1) (right := 2) (thenCode := []) (elseCode := [])
    (returns := []) (hpc := hpc) (hzero := hzero)
  · simp [wordConditionOperands, registerOfNat]
  · exact ⟨state, by simp [evalWordFunction], by constructor <;> rfl⟩
  · exact ⟨state, by simp [evalWordFunction], by constructor <;> rfl⟩
  · simp
  · simp
  · decide

example (state : State 8) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    ∃ sourceState machineState,
      evalWordFunction state
          ((.ite .equal 1 (.reg 2) .skip .skip) : WordProg (Word 8)) =
        some (sourceState, []) ∧
      wordFunctionToRiscVWithCalls (⟨[]⟩ : WordCallContext 8)
          ((.ite .equal 1 (.reg 2) .skip .skip) : WordProg (Word 8)) =
        some ([.branchNe 1 2 (BitVec.ofNat 8 8),
          .branchEq 0 0 (BitVec.ofNat 8 4)], []) ∧
      executeCodeUntil 3 0 (BitVec.ofNat 8 8)
          [.branchNe 1 2 (BitVec.ofNat 8 8),
            .branchEq 0 0 (BitVec.ofNat 8 4)] state = some machineState ∧
      StateDataRelation sourceState machineState := by
  apply wordFunctionToRiscVWithCalls_ite_source_machine_of_nonbranching
    (context := (⟨[]⟩ : WordCallContext 8)) (state := state)
    (operator := .equal) (condition := 1) (source := 2)
    (thenBranch := (.skip : WordProg (Word 8)))
    (elseBranch := (.skip : WordProg (Word 8)))
    (branchLeft := 1) (right := 2) (thenCode := []) (elseCode := [])
    (returnRegisters := []) (returnValues := []) (hpc := hpc) (hzero := hzero)
  · simp [wordConditionOperands, registerOfNat]
  · simp [wordFunctionToRiscVWithCalls]
  · simp [wordFunctionToRiscVWithCalls]
  · exact ⟨state, by simp [evalWordFunction], by constructor <;> rfl⟩
  · exact ⟨state, by simp [evalWordFunction], by constructor <;> rfl⟩
  · simp
  · simp
  · decide

example (state : State 8) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    ∃ sourceState machineState,
      evalWordFunction state
          ((.ite .equal 1 (.reg 2)
            (.assign 3 (.const (1 : Word 8)))
            (.assign 3 (.const (2 : Word 8)))) : WordProg (Word 8)) =
        some (sourceState, []) ∧
      wordFunctionToRiscVWithCalls (⟨[]⟩ : WordCallContext 8)
          ((.ite .equal 1 (.reg 2)
            (.assign 3 (.const (1 : Word 8)))
            (.assign 3 (.const (2 : Word 8)))) : WordProg (Word 8)) =
        some ([.branchNe 1 2 (BitVec.ofNat 8 12), .addi 3 0 1,
          .branchEq 0 0 (BitVec.ofNat 8 8), .addi 3 0 2], []) ∧
      executeCodeUntil 5 0 (BitVec.ofNat 8 16)
          [.branchNe 1 2 (BitVec.ofNat 8 12), .addi 3 0 1,
            .branchEq 0 0 (BitVec.ofNat 8 8), .addi 3 0 2] state =
        some machineState ∧
      StateDataRelation sourceState machineState := by
  apply wordFunctionToRiscVWithCalls_ite_source_machine_of_nonbranching
    (context := (⟨[]⟩ : WordCallContext 8)) (state := state)
    (operator := .equal) (condition := 1) (source := 2)
    (thenBranch := (.assign 3 (.const (1 : Word 8))))
    (elseBranch := (.assign 3 (.const (2 : Word 8))))
    (branchLeft := 1) (right := 2)
    (thenCode := [.addi 3 0 1]) (elseCode := [.addi 3 0 2])
    (returnRegisters := []) (returnValues := []) (hpc := hpc) (hzero := hzero)
  · simp [wordConditionOperands, registerOfNat]
  · simp [wordFunctionToRiscVWithCalls, wordExpToInstructions,
      wordExpToInstruction, registerOfNat]
  · simp [wordFunctionToRiscVWithCalls, wordExpToInstructions,
      wordExpToInstruction, registerOfNat]
  · exact ⟨execute state (.addi 3 0 1),
      by simp [evalWordFunction, wordExpToInstructions,
        wordExpToInstruction, registerOfNat], by constructor <;> rfl⟩
  · exact ⟨execute state (.addi 3 0 2),
      by simp [evalWordFunction, wordExpToInstructions,
        wordExpToInstruction, registerOfNat], by constructor <;> rfl⟩
  · decide
  · decide
  · decide

example (state : State 64) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    (executeCode 5 0
      [.branchNe 1 2 (BitVec.ofNat 64 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 64 8), .addi 3 0 2] state).map
      (fun state => readRegister state 3) =
      if readRegister state 1 == readRegister state 2 then
        some (1 : Word 64)
      else
        some (2 : Word 64) := by
  exact executeCode_ite_assign state hpc hzero (by decide)

example (state : State 32) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    (executeCode 5 0
      [.branchNe 1 2 (BitVec.ofNat 32 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2] state).map
      (fun state => readRegister state 3) =
      if readRegister state 1 == readRegister state 2 then
        some (1 : Word 32)
      else
        some (2 : Word 32) := by
  exact executeCode_ite_assign state hpc hzero (by decide)

example (state : State 32) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    (evalWordFunction state
      ((.ite .equal 1 (.reg 2)
        (.assign 3 (.const (1 : Word 32)))
        (.assign 3 (.const (2 : Word 32)))) : WordProg (Word 32))).map
      (fun result => readRegister result.1 3) =
      (executeCode 5 0
        [.branchNe 1 2 (BitVec.ofNat 32 12), .addi 3 0 1,
          .branchEq 0 0 (BitVec.ofNat 32 8), .addi 3 0 2] state).map
        (fun finalState => readRegister finalState 3) := by
  exact evalWordFunction_ite_assign_riscV_register state hpc hzero (by decide)

example (state : State 8) (operator : Cmp) (left right : Fin 32)
    (hpc : state.pc = 0) :
    executeCodeUntil 6 0 (BitVec.ofNat 8 20)
        (riscVBranchFalseInstruction operator left right (BitVec.ofNat 8 16) ::
          [.addi 1 0 7, .addi 2 1 3] ++
          [.branchEq 0 0 (BitVec.ofNat 8 8)] ++
          [.addi 3 0 2]) state |>.isSome := by
  have hrun := executeCodeUntil_conditional_of_nonbranching state operator left right
    [.addi 1 0 7, .addi 2 1 3] [.addi 3 0 2] hpc (by
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | rfl | hfalse
      · rfl
      · rfl
      · contradiction) (by
      intro instruction hinstruction
      simp only [List.mem_singleton] at hinstruction
      subst instruction
      rfl) (by decide)
  by_cases hcondition : riscVCondition state operator left right
  · simpa [List.length_cons, Option.isSome, hcondition] using
      congrArg Option.isSome hrun
  · simpa [List.length_cons, Option.isSome, hcondition] using
      congrArg Option.isSome hrun

example :
    executeCodeUntilWithFfiCounted testNoFfiHost 5 0 (16#8)
        [riscVBranchFalseInstruction .equal 0 0 (BitVec.ofNat 8 12),
          .addi 1 0 7, .branchEq 0 0 (BitVec.ofNat 8 8), .addi 2 0 9]
        (zeroState 8) =
      some
        (execute (execute (execute (zeroState 8)
          (riscVBranchFalseInstruction .equal 0 0 (BitVec.ofNat 8 12)))
          (.addi 1 0 7))
          (.branchEq 0 0 (BitVec.ofNat 8 8)), 3) := by
  have hrun := executeCodeUntilWithFfiCounted_conditional_of_nonbranching
    (host := testNoFfiHost) (state := zeroState 8) (operator := .equal)
    (left := 0) (right := 0) (thenCode := [.addi 1 0 7])
    (elseCode := [.addi 2 0 9])
    (thenState := execute (execute (zeroState 8)
      (riscVBranchFalseInstruction .equal 0 0 (BitVec.ofNat 8 12)))
      (.addi 1 0 7))
    (elseState := execute (execute (zeroState 8)
      (riscVBranchFalseInstruction .equal 0 0 (BitVec.ofNat 8 12)))
      (.addi 2 0 9))
    (thenCount := 1) (elseCount := 1)
    (hpc := by rfl)
    (hthenAdvance := by
      intro current instruction hinstruction next hstep
      have hinstruction' : instruction = .addi 1 0 7 := by
        simpa using hinstruction
      subst instruction
      simp [executeWithFfi, execute, writeRegister, nextPc] at hstep
      simpa [executeWithFfi, execute, writeRegister, nextPc] using
        (congrArg State.pc hstep).symm)
    (helseAdvance := by
      intro current instruction hinstruction next hstep
      have hinstruction' : instruction = .addi 2 0 9 := by
        simpa using hinstruction
      subst instruction
      simp [executeWithFfi, execute, writeRegister, nextPc] at hstep
      simpa [executeWithFfi, execute, writeRegister, nextPc] using
        (congrArg State.pc hstep).symm)
    (hthenResult := by rfl) (helseResult := by rfl) (hbound := by decide)
  simpa [riscVCondition] using hrun

end Flapjack.Test.CorrectnessConditional
