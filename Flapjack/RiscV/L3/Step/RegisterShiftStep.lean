import Flapjack.RiscV.L3.Step.ImmediateShiftStep
import Flapjack.RiscV.L3.Defs.RegisterShift

/-! Evaluated original `riscv_stepScript.sml` register-shift instruction
theorems (`SLL`, `SRL`, `SRA`, lines 867-869) over the literal native
`dfn'SLL`/`dfn'SRL`/`dfn'SRA` equations, together with their generated
`rd = 0` companions (`SLL_NOP`/`SRL_NOP`/`SRA_NOP`).  Each write theorem keeps
the original `ArchBase <> 1w` invalid-selector hypothesis and the `rd <> 0w`
destination hypothesis; the companions carry the same mode hypothesis plus
`rd = 0w`.  The RV32I branch uses the low-5-bit count while the RV64 path uses
the low-6-bit count, and `SRL`/`SRA` widen the low word in RV32. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLL"]
theorem dfnSLL (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SLL» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
             (if rs1 = 0 then 0 else s.c_gpr s.procID rs1) <<<
               (if rs2 = 0 then 0 else BitVec.setWidth 64 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat
           else
             (if rs1 = 0 then 0 else s.c_gpr s.procID rs1) <<<
               (if rs2 = 0 then 0 else BitVec.setWidth 64 (holWordExtract 6 5 0 (s.c_gpr s.procID rs2))).toNat)
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SLL», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_shiftLeft, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRL"]
theorem dfnSRL (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRL» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
             BitVec.setWidth 64
               ((if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) >>>
                 (if rs2 = 0 then 0 else BitVec.setWidth 32 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat)
           else
             (if rs1 = 0 then 0 else s.c_gpr s.procID rs1) >>>
               (if rs2 = 0 then 0 else BitVec.setWidth 64 (holWordExtract 6 5 0 (s.c_gpr s.procID rs2))).toNat)
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRL», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_ushiftRight, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRA"]
theorem dfnSRA (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SRA» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
             BitVec.signExtend 64
               (BitVec.sshiftRight
                 (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
                 (if rs2 = 0 then 0 else BitVec.setWidth 32 (holWordExtract 5 4 0 (s.c_gpr s.procID rs2))).toNat)
           else
             BitVec.sshiftRight (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
               (if rs2 = 0 then 0 else BitVec.setWidth 64 (holWordExtract 6 5 0 (s.c_gpr s.procID rs2))).toNat)
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SRA», in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [«write'GPR», «write'gpr», GPR, gpr, beq_iff_eq, ne_eq]
  all_goals by_cases hr : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, BitVec.zero_sshiftRight, BitVec.toNat_setWidth]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SLL_NOP"]
theorem dfnSLLNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SLL» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SLL», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRL_NOP"]
theorem dfnSRLNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRL» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SRL», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SRA_NOP"]
theorem dfnSRANop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SRA» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SRA», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

end Flapjack.RiscV.L3.Step
