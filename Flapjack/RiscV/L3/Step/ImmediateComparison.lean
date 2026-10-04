import Flapjack.RiscV.L3.Defs.SetLess

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Local derivation of the original step evaluator's mode rewrite. The
ArchBase exclusion is an original SLTI/SLTIU hypothesis, propagated by HOL's
not1 and in32BitMode EV. This helper claims no separately exported original. -/
private theorem comparison_mode (s : riscv_state)
    (h : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    in32BitMode () s = ((s.c_MCSR s.procID).mcpuid.ArchBase == 0#2, s) := by
  let ab := (s.c_MCSR s.procID).mcpuid.ArchBase
  have bound : ab.toNat < 4 := ab.isLt
  have neq : ab.toNat ≠ 1 := by
    intro e
    apply h
    apply BitVec.eq_of_toNat_eq
    exact e
  have choices : ab.toNat = 0 ∨ ab.toNat = 2 ∨ ab.toNat = 3 := by omega
  rcases choices with e | e | e
  all_goals
    have eq := BitVec.ofNat_toNat 2 ab
    rw [e] at eq
    have eq' := eq.symm
    simp only [BitVec.setWidth_eq, ab] at eq'
    simp [in32BitMode, curArch, architecture, MCSR, eq']

/-- Original evaluated SLTI equation (source839), retaining BOTH original
hypotheses, rd<>0 and ArchBase<>1. RV32 reads sign-extend the low32 bits;
source-zero, all register aliases and the full resulting native record remain.
This declaration uses only word/register/mode operations and has no inherited
real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTI"]
theorem dfnSltI (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTI» (rd, rs1, imm) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.slt
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (imm.signExtend 64)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTI», comparison_mode s arch]
  by_cases zero : rs1 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero, mode, beq_iff_eq,
        holWordExtract]

/-- Original evaluated SLTIU equation (source840), retaining BOTH original
hypotheses, rd<>0 and ArchBase<>1. RV32 reads sign-extend the low32 bits;
source-zero, all register aliases and the full resulting native record remain.
This declaration uses only word/register/mode operations and has no inherited
real arithmetic assumption. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTIU"]
theorem dfnSltIU (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTIU» (rd, rs1, imm) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.ult
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (imm.signExtend 64)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTIU», comparison_mode s arch]
  by_cases zero : rs1 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero, mode, beq_iff_eq,
        holWordExtract]

end Flapjack.RiscV.L3.Step
