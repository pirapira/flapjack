import Flapjack.RiscV.CorrectnessCondition

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (operator : Cmp)
    (condition source : Nat)
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.reg source) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.reg source) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_register_sound state operator condition source hzero
    branchLeft right prelude hoperands

example [NeZero width] (state : State width) (operator : Cmp)
    (condition : Nat) (branchLeft right : Fin 32)
    (prelude : List (Instruction width)) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.imm 0) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.imm 0) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_immediate_zero_sound state operator condition hzero
    branchLeft right prelude hoperands

example [NeZero width] (state : State width) (operator : Cmp)
    (condition : Nat) (value : Word width) (branchLeft right : Fin 32)
    (prelude : List (Instruction width)) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.imm value) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.imm value) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_immediate_sound state operator condition value hzero
    branchLeft right prelude hoperands

example [NeZero width] (state : State width) (operator : Cmp)
    (condition : Nat) (rightValue : WordRegImm (Word width))
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition rightValue =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition rightValue =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_sound state operator condition rightValue hzero
    branchLeft right prelude hoperands

example (state : State 8) (hzero : ZeroRegister state) :
    evalWordCondition state .test 1 (.reg 2) =
      riscVCondition (executeInstructions state [.and 1 1 2]) .test 1 0 := by
  apply wordConditionOperands_sound state .test 1 (.reg 2) hzero 1 0
    [.and 1 1 2]
  simp [wordConditionOperands, registerOfNat]

example (state : State 8) (hzero : ZeroRegister state) :
    evalWordCondition state .equal 1 (.imm (7 : Word 8)) =
      riscVCondition (executeInstructions state [.ori 31 0 7]) .equal 1 31 := by
  apply wordConditionOperands_sound state .equal 1 (.imm (7 : Word 8)) hzero 1 31
    [.ori 31 0 7]
  simp [wordConditionOperands, registerOfNat]

end Flapjack.RiscV
