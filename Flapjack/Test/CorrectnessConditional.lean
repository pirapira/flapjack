import Flapjack.RiscV.CorrectnessConditional

namespace Flapjack.Test.CorrectnessConditional

open Flapjack Flapjack.RiscV

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
    wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word 64)))
          (.assign 3 (.const (2 : Word 64)))) : WordProg (Word 64)) =
      some ([.branchNe 1 2 (BitVec.ofNat 64 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 64 8), .addi 3 0 2], []) := by
  exact wordFunctionToRiscV_ite_assign

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

end Flapjack.Test.CorrectnessConditional
