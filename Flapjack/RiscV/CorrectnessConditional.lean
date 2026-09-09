import Flapjack.RiscV.CorrectnessCode

/-!
Machine-level control-flow correctness for the smallest conditional layout
emitted by the Word backend.  The general lowering uses the same layout:
branch over the then block, execute an unconditional jump over the else block,
then stop at the first byte after the conditional.
-/

namespace Flapjack.RiscV

def advancesPc [NeZero width] (instruction : Instruction width) : Prop :=
  ∀ state : State width, (execute state instruction).pc = nextPc state

theorem executeCode_conditional_single
    [NeZero width] (state : State width) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction width)
    (hpc : state.pc = 0)
    (hwidth : 5 ≤ width)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat width 8)
        , elseInstruction ] state =
      if riscVCondition state operator left right then
        some (execute
          (execute
            (execute state
              (riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)))
            thenInstruction)
          (.branchEq 0 0 (BitVec.ofNat width 8)))
      else
        some (execute
          (execute state
            (riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)))
          elseInstruction) := by
  let branch := riscVBranchFalseInstruction operator left right (BitVec.ofNat width 12)
  let jump : Instruction width := .branchEq 0 0 (BitVec.ofNat width 8)
  have hbranch := execute_riscVBranchFalse_pc state operator left right
    (BitVec.ofNat width 12)
  have hpow : 2 ^ 5 ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by decide) hwidth
  have hbound4 : 4 < 2 ^ width := by omega
  have hbound8 : 8 < 2 ^ width := by omega
  have hbound12 : 12 < 2 ^ width := by omega
  have hbound16 : 16 < 2 ^ width := by omega
  by_cases hcondition : riscVCondition state operator left right
  · have hbranchPc : (execute state branch).pc = 4 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have hthenPc : (execute (execute state branch) thenInstruction).pc = 8 := by
      rw [hthen]
      simp only [nextPc, hbranchPc]
      change BitVec.ofNat width 4 + BitVec.ofNat width 4 = BitVec.ofNat width 8
      rw [show (8 : Nat) = 4 + 4 by omega, BitVec.ofNat_add]
    have hjumpPc :
        (execute (execute (execute state branch) thenInstruction) jump).pc = 16 := by
      change (execute (execute (execute state branch) thenInstruction)
        (.branchEq 0 0 (BitVec.ofNat width 8))).pc = 16
      rw [execute_branchEq_pc, hthenPc]
      simp
      change BitVec.ofNat width 8 + BitVec.ofNat width 8 = BitVec.ofNat width 16
      rw [show (16 : Nat) = 8 + 8 by omega, BitVec.ofNat_add]
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) := by
      simp [executeCode, hbranchPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound4]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hthenPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound8]
    have hstep4 :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) =
          some (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hjumpPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3, hstep4]
    simp [hcondition, branch, jump]
  · have hbranchPc : (execute state branch).pc = 12 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have helsePc : (execute (execute state branch) elseInstruction).pc = 16 := by
      rw [helse]
      simp only [nextPc, hbranchPc]
      change BitVec.ofNat width 12 + BitVec.ofNat width 4 = BitVec.ofNat width 16
      rw [show (16 : Nat) = 12 + 4 by omega, BitVec.ofNat_add]
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, hbranchPc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound12]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3]
    have hend :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          some (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbound16]
    rw [hend]
    simp [hcondition, branch]

theorem wordFunctionToRiscV_ite_assign [NeZero width] :
    wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word width)))
          (.assign 3 (.const (2 : Word width)))) : WordProg (Word width)) =
      some ([.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2], []) := by
  simp [wordFunctionToRiscV, wordConditionOperands, wordExpToInstructions,
    wordExpToInstruction, registerOfNat]

theorem executeCode_ite_assign [NeZero width] (state : State width) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) (hwidth : 5 ≤ width) :
    (executeCode 5 0
      [.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] state).map
      (fun state => readRegister state 3) =
      if readRegister state 1 == readRegister state 2 then
        some (1 : Word width)
      else
        some (2 : Word width) := by
  have hzero' : state.registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzero
  have hthen : advancesPc (.addi 3 0 (1 : Word width)) := by
    intro state
    simp [execute, writeRegister, nextPc]
  have helse : advancesPc (.addi 3 0 (2 : Word width)) := by
    intro state
    simp [execute, writeRegister, nextPc]
  have hrun := executeCode_conditional_single state .equal 1 2
    (.addi 3 0 (1 : Word width)) (.addi 3 0 (2 : Word width)) hpc
    hwidth hthen helse
  by_cases hcondition : readRegister state 1 = readRegister state 2
  · have hrisc : riscVCondition state .equal 1 2 = true := by
      simp [riscVCondition, hcondition]
    have hcondition' : state.registers 1 = state.registers 2 := by
      simpa [readRegister] using hcondition
    rw [if_pos hrisc] at hrun
    simp only [riscVBranchFalseInstruction] at hrun
    rw [hrun]
    simp [execute, writeRegister, readRegister, nextPc, hzero']
    intro hne
    exact (hne hcondition').elim
  · have hrisc : ¬riscVCondition state .equal 1 2 = true := by
      simp [riscVCondition, hcondition]
    have hcondition' : ¬state.registers 1 = state.registers 2 := by
      intro heq
      apply hcondition
      simpa [readRegister] using heq
    rw [if_neg hrisc] at hrun
    simp only [riscVBranchFalseInstruction] at hrun
    rw [hrun]
    simp [execute, writeRegister, readRegister, nextPc, hzero']
    intro heq
    exact (hcondition' heq).elim

theorem evalWordFunction_ite_assign_riscV_register [NeZero width]
    (state : State width) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) (hwidth : 5 ≤ width) :
    (evalWordFunction state
      ((.ite .equal 1 (.reg 2)
        (.assign 3 (.const (1 : Word width)))
        (.assign 3 (.const (2 : Word width)))) : WordProg (Word width))).map
      (fun result => readRegister result.1 3) =
      (executeCode 5 0
        [.branchNe 1 2 (BitVec.ofNat width 12), .addi 3 0 1,
          .branchEq 0 0 (BitVec.ofNat width 8), .addi 3 0 2] state).map
        (fun finalState => readRegister finalState 3) := by
  have hzero' : state.registers 0 = 0 := by
    simpa [ZeroRegister, readRegister] using hzero
  rw [executeCode_ite_assign state hpc hzero hwidth]
  by_cases hcondition : state.registers 1 = state.registers 2
  · simp [evalWordFunction, evalWordCondition, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, executeInstructions, execute,
      writeRegister, readRegister, nextPc, hzero', hcondition]
  · simp [evalWordFunction, evalWordCondition, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, executeInstructions, execute,
      writeRegister, readRegister, nextPc, hzero', hcondition]

end Flapjack.RiscV
