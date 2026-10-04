import Flapjack.RiscV.L3.Step.RegisterShiftStep

/-! Evaluated original `riscv_stepScript.sml` word-shift instruction theorems
(immediate `SLLIW`/`SRLIW`/`SRAIW`, lines 847-849, and register `SLLW`/`SRLW`/
`SRAW`, lines 870-872) over the literal native `dfn'SLLIW`/`dfn'SRLIW`/
`dfn'SRAIW`/`dfn'SLLW`/`dfn'SRLW`/`dfn'SRAW` equations, together with the
generated `rd = 0` companions.  Each write theorem keeps the original
RV32-exclusion hypothesis `ArchBase <> 0w`, the invalid-selector hypothesis
`ArchBase <> 1w`, and the destination hypothesis `rd <> 0w`; the companions
carry the same mode hypotheses plus `rd = 0w`.  All word forms operate on the
low 32 bits and sign-extend the result. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLLIW"]
theorem dfnSLLIW (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SLLIW» (rd, (rs1, imm)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if rs1 = 0 then 0
           else BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1) <<< imm.toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SLLIW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> simp_all [holWordExtract, BitVec.zero_shiftLeft]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRLIW"]
theorem dfnSRLIW (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRLIW» (rd, (rs1, imm)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if rs1 = 0 then 0
           else BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1) >>> imm.toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRLIW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> simp_all [holWordExtract, BitVec.zero_ushiftRight]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRAIW"]
theorem dfnSRAIW (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRAIW» (rd, (rs1, imm)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64 (BitVec.sshiftRight
            (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) imm.toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRAIW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> simp_all [holWordExtract, BitVec.zero_sshiftRight]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLLW"]
theorem dfnSLLW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SLLW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64
            ((if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) <<<
              (if rs2 = 0 then 0 else BitVec.setWidth 32 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SLLW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_shiftLeft, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRLW"]
theorem dfnSRLW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRLW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64
            ((if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) >>>
              (if rs2 = 0 then 0 else BitVec.setWidth 32 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRLW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_ushiftRight, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRAW"]
theorem dfnSRAW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRAW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64
            (BitVec.sshiftRight
              (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
              (if rs2 = 0 then 0 else BitVec.setWidth 32 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRAW», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_sshiftRight, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLLIW_NOP"]
theorem dfnSLLIWNop (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SLLIW» (rd, (rs1, imm)) s = s := by
  simp only [«dfn'SLLIW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRLIW_NOP"]
theorem dfnSRLIWNop (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRLIW» (rd, (rs1, imm)) s = s := by
  simp only [«dfn'SRLIW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRAIW_NOP"]
theorem dfnSRAIWNop (rd rs1 : BitVec 5) (imm : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRAIW» (rd, (rs1, imm)) s = s := by
  simp only [«dfn'SRAIW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLLW_NOP"]
theorem dfnSLLWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SLLW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SLLW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRLW_NOP"]
theorem dfnSRLWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRLW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SRLW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRAW_NOP"]
theorem dfnSRAWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRAW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SRAW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

end Flapjack.RiscV.L3.Step
