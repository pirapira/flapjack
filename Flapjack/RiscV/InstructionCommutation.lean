import Flapjack.RiscV.InstructionRelabel

/-!
# RISC-V execution commutation for control-flow instructions

The instruction relabeling is intended to be applied at the boundary between
CakeML's stack-register convention and the hardware model.  This file starts
the executable correctness bridge with instructions that only update the
program counter: branches and `ecall` do not need the destination-register
side conditions required by arithmetic and load instructions.
-/

namespace Flapjack.RiscV

variable {width : Nat}

theorem execute_transferState_branchEq_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchEq sourceLeft sourceRight offset)) =
      transferState (execute state (.branchEq sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]

theorem execute_transferState_branchNe_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchNe sourceLeft sourceRight offset)) =
      transferState (execute state (.branchNe sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]

theorem execute_transferState_branchLt_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchLt sourceLeft sourceRight offset)) =
      transferState (execute state (.branchLt sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]
  split <;> simp_all
  all_goals split <;> simp_all

theorem execute_transferState_branchGe_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchGe sourceLeft sourceRight offset)) =
      transferState (execute state (.branchGe sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]
  split <;> simp_all
  all_goals split <;> simp_all

theorem execute_transferState_branchLtU_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchLtU sourceLeft sourceRight offset)) =
      transferState (execute state (.branchLtU sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]
  rfl

theorem execute_transferState_branchGeU_commutes (state : State width)
    (sourceLeft sourceRight : Fin 32) (offset : Word width) :
    execute (transferState state)
        (relabelInstruction (.branchGeU sourceLeft sourceRight offset)) =
      transferState (execute state (.branchGeU sourceLeft sourceRight offset)) := by
  cases state
  simp [relabelInstruction, execute, transferState, readRegister, riscvInverse_riscvForward, nextPc]
  rfl

theorem execute_transferState_ecall_commutes (state : State width) :
    execute (transferState state) (relabelInstruction (.ecall : Instruction width)) =
      transferState (execute state .ecall) := by
  cases state
  simp [relabelInstruction, execute, transferState, nextPc]

end Flapjack.RiscV
