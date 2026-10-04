import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.ConditionalBranch

/-! Full original evaluated `riscv_stepScript.sml` conditional-branch equations
(`BEQ`/`BNE`/`BLT`/`BLTU`/`BGE`/`BGEU`, source `class (rs1,rs2,offs)` at
riscv_stepScript.sml:891-898).  Each theorem is UNCONDITIONAL apart from the
original invalid-selector hypothesis `ArchBase <> 1w`; the whole native record
is returned and the taken path writes `SOME (BranchTo (PC + sw2sw offs << 1))`
into `c_NextFetch`, with no JAL-style alignment check and no GPR/PC change.

The operand expression `branchOperand` is the literal HOL evaluated operand: the
second `in32BitMode` reading agrees with the first, so `if rs = 0 then 0 else if
ArchBase = 0 then sw2sw(low32 register) else register`.  For `BEQ`/`BNE` the
printed nested form has the two readings of `ArchBase` identical, so comparison
is exactly `branchOperand rs1 = branchOperand rs2`. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

private def branchOperand (rs : BitVec 5) (s : riscv_state) : BitVec 64 :=
  if rs = 0 then 0
  else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
    BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs))
  else s.c_gpr s.procID rs

private theorem holUpdate_self {α β : Type} [DecidableEq α] (a : α) (f : α → β) :
    holUpdate a (f a) f = f := by
  funext c
  simp only [holUpdate]
  by_cases h : a = c <;> simp_all

private theorem ite_holUpdate (C : Prop) [Decidable C] (s : riscv_state)
    (v : Option TransferControl) :
    (if C then { s with c_NextFetch := holUpdate s.procID v s.c_NextFetch } else s) =
      { s with
        c_NextFetch := holUpdate s.procID (if C then v else s.c_NextFetch s.procID) s.c_NextFetch } := by
  by_cases h : C <;> simp_all [holUpdate_self]

private theorem ite_holUpdate_not (C : Prop) [Decidable C] (s : riscv_state)
    (v : Option TransferControl) :
    (if C then s else { s with c_NextFetch := holUpdate s.procID v s.c_NextFetch }) =
      { s with
        c_NextFetch := holUpdate s.procID (if C then s.c_NextFetch s.procID else v) s.c_NextFetch } := by
  by_cases h : C <;> simp_all [holUpdate_self]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BEQ"]
theorem dfnBEQ (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BEQ» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if branchOperand rs1 s == branchOperand rs2 s then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BEQ», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BNE"]
theorem dfnBNE (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BNE» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if !(branchOperand rs1 s == branchOperand rs2 s) then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BNE», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate_not] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BLT"]
theorem dfnBLT (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BLT» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if BitVec.slt (branchOperand rs1 s) (branchOperand rs2 s) then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BLT», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BLTU"]
theorem dfnBLTU (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BLTU» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if BitVec.ult (branchOperand rs1 s) (branchOperand rs2 s) then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BLTU», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BGE"]
theorem dfnBGE (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BGE» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if BitVec.sle (branchOperand rs2 s) (branchOperand rs1 s) then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BGE», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "BGEU"]
theorem dfnBGEU (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    «dfn'BGEU» (rs1, (rs2, offs)) s =
      { s with
        c_NextFetch := holUpdate s.procID
          (if !(BitVec.ult (branchOperand rs1 s) (branchOperand rs2 s)) then
             some (TransferControl.BranchTo (PC s + (BitVec.signExtend 64 offs <<< 1)))
           else s.c_NextFetch s.procID) s.c_NextFetch } := by
  simp only [«dfn'BGEU», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [branchOperand, branchTo, «write'NextFetch», GPR, gpr, beq_iff_eq, holWordExtract, ite_holUpdate] <;>
    by_cases hr1 : rs1 = 0 <;> by_cases hr2 : rs2 = 0 <;> simp_all

end Flapjack.RiscV.L3.Step
