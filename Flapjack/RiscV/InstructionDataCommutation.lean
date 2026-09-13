import Flapjack.RiscV.InstructionRelabel

/-!
# RISC-V execution commutation for arithmetic, load, and store instructions

`Flapjack.RiscV.InstructionCommutation` covers the control-flow instructions,
which only update the program counter.  This file completes the executable
bridge for the data instructions by deriving the destination-register side
conditions from the `instructionWrites` table and the general commutation
theorem `execute_transfer_relabel`.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- Commutation for an instruction that writes exactly one destination register
which avoids both hardware zero (`x0`) and the internal Cake zero register. -/
theorem execute_transfer_relabel_singleton (state : State width) (instruction : Instruction width)
    (destination : Fin 32) (hwrites : instructionWrites instruction = [destination])
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state) (relabelInstruction instruction) =
      transferState (execute state instruction) := by
  apply execute_transfer_relabel
  · intro register member
    rw [hwrites, List.mem_singleton] at member
    subst member
    exact hzero
  · intro register member
    rw [hwrites, List.mem_singleton] at member
    subst member
    exact hname

/-- Commutation for an instruction that writes no register (stores and similar). -/
theorem execute_transfer_relabel_noWrites (state : State width) (instruction : Instruction width)
    (hwrites : instructionWrites instruction = []) :
    execute (transferState state) (relabelInstruction instruction) =
      transferState (execute state instruction) := by
  apply execute_transfer_relabel
  · intro register member
    rw [hwrites] at member
    simp at member
  · intro register member
    rw [hwrites] at member
    simp at member

theorem execute_transferState_add_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.add destination sourceLeft sourceRight)) =
      transferState (execute state (.add destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_sub_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.sub destination sourceLeft sourceRight)) =
      transferState (execute state (.sub destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_and_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.and destination sourceLeft sourceRight)) =
      transferState (execute state (.and destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_or_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.or destination sourceLeft sourceRight)) =
      transferState (execute state (.or destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_xor_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.xor destination sourceLeft sourceRight)) =
      transferState (execute state (.xor destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_mul_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.mul destination sourceLeft sourceRight)) =
      transferState (execute state (.mul destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_sll_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.sll destination sourceLeft sourceRight)) =
      transferState (execute state (.sll destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_srl_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.srl destination sourceLeft sourceRight)) =
      transferState (execute state (.srl destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_sra_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.sra destination sourceLeft sourceRight)) =
      transferState (execute state (.sra destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_slt_commutes (state : State width)
    (destination sourceLeft sourceRight : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.slt destination sourceLeft sourceRight)) =
      transferState (execute state (.slt destination sourceLeft sourceRight)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_addi_commutes (state : State width)
    (destination source : Fin 32) (immediate : Word width)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.addi destination source immediate)) =
      transferState (execute state (.addi destination source immediate)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_lui_commutes (state : State width)
    (destination : Fin 32) (immediate : Word width)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.lui destination immediate)) =
      transferState (execute state (.lui destination immediate)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_loadWord_commutes (state : State width)
    (destination address : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.loadWord destination address)) =
      transferState (execute state (.loadWord destination address)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_loadByte_commutes (state : State width)
    (destination address : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.loadByte destination address)) =
      transferState (execute state (.loadByte destination address)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_load32_commutes (state : State width)
    (destination address : Fin 32)
    (hzero : riscvForward destination ≠ 0) (hname : destination ≠ 0) :
    execute (transferState state)
        (relabelInstruction (.load32 destination address)) =
      transferState (execute state (.load32 destination address)) :=
  execute_transfer_relabel_singleton state _ destination
    (by simp [instructionWrites]) hzero hname

theorem execute_transferState_storeWord_commutes (state : State width)
    (source address : Fin 32) :
    execute (transferState state)
        (relabelInstruction (.storeWord source address)) =
      transferState (execute state (.storeWord source address)) :=
  execute_transfer_relabel_noWrites state _ (by simp [instructionWrites])

theorem execute_transferState_storeByte_commutes (state : State width)
    (source address : Fin 32) :
    execute (transferState state)
        (relabelInstruction (.storeByte source address)) =
      transferState (execute state (.storeByte source address)) :=
  execute_transfer_relabel_noWrites state _ (by simp [instructionWrites])

theorem execute_transferState_storeHalf_commutes (state : State width)
    (source address : Fin 32) :
    execute (transferState state)
        (relabelInstruction (.storeHalf source address)) =
      transferState (execute state (.storeHalf source address)) :=
  execute_transfer_relabel_noWrites state _ (by simp [instructionWrites])

end Flapjack.RiscV
