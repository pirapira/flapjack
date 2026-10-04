import Flapjack.RiscV.L3.Defs.SetLess

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
set_option autoImplicit false

/-- Local derivation of the original step evaluator's mode rewrite. The
ArchBase exclusion is an original SLT/SLTU hypothesis, propagated by HOL's
not1 and in32BitMode EV. This helper claims no separately exported original. -/
private theorem registerComparisonMode (s : riscv_state)
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

/-- Full original SLT register comparison: original destination and ArchBase
hypotheses, both source-zero reads, RV32 sign extension, and whole state update.
All aliases and all remaining architecture modes are unrestricted. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLT"]
theorem dfnSlt (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLT» (rd, rs1, rs2) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.slt
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).signExtend 64
             else s.c_gpr s.procID rs1)
            (if rs2 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)).signExtend 64
             else s.c_gpr s.procID rs2)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLT», registerComparisonMode s arch]
  by_cases zero1 : rs1 = 0#5 <;>
    by_cases zero2 : rs2 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero1, zero2, mode,
        beq_iff_eq, holWordExtract]

/-- Full original SLTU register comparison: original destination and ArchBase
hypotheses, both source-zero reads, RV32 zero extension, and whole state update.
All aliases and all remaining architecture modes are unrestricted. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTU"]
theorem dfnSltU (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd ≠ 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTU» (rd, rs1, rs2) s =
      {s with
        c_gpr := holUpdate s.procID
          (holUpdate rd
          (holV2w 64 [BitVec.ult
            (if rs1 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)).setWidth 64
             else s.c_gpr s.procID rs1)
            (if rs2 = 0#5 then 0#64
             else if (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 then
               (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)).setWidth 64
             else s.c_gpr s.procID rs2)])
          (s.c_gpr s.procID)) s.c_gpr} := by
  simp only [«dfn'SLTU», registerComparisonMode s arch]
  by_cases zero1 : rs1 = 0#5 <;>
    by_cases zero2 : rs2 = 0#5 <;>
    by_cases mode : (s.c_MCSR s.procID).mcpuid.ArchBase = 0#2 <;>
      simp [«write'GPR», «write'gpr», GPR, gpr, h, zero1, zero2, mode,
        beq_iff_eq, holWordExtract]

/-- Original generated SLT_NOP companion. The destination-zero and
ArchBase exclusions are both retained; the two mode queries have no effect
under that original guard, and the destination write is suppressed. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLT_NOP"]
theorem dfnSltNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLT» (rd, rs1, rs2) s = s := by
  simp [«dfn'SLT», registerComparisonMode s arch, «write'GPR», h]

/-- Original generated SLTU_NOP companion. The destination-zero and
ArchBase exclusions are both retained; the two mode queries have no effect
under that original guard, and the destination write is suppressed. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLTU_NOP"]
theorem dfnSltUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'SLTU» (rd, rs1, rs2) s = s := by
  simp [«dfn'SLTU», registerComparisonMode s arch, «write'GPR», h]

end Flapjack.RiscV.L3.Step
