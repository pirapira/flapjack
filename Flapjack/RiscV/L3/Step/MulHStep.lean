import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.Multiply

/-! Evaluated original `riscv_stepScript.sml` high-multiply step theorems
(`MULH`/`MULHU`/`MULHSU`, lines 874-886).  Each keeps the original
invalid-selector mode hypothesis together with the destination hypothesis,
performs the original three mode queries, forms the 128-bit intermediate
product with the literal per-operand signedness, selects the RV32 or RV64 high
half and extends it.  The generated `rd = 0w` companions retain the mode
hypothesis. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Signed literal HOL operand of the high-multiply families: the zero register
reads as zero, RV32 sign-extends the low 32 bits through `word64` into the
128-bit product, RV64 sign-extends the full register. -/
private def mulhOpS (rs : BitVec 5) (s : riscv_state) : BitVec 128 :=
  if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
    BitVec.signExtend 128 (BitVec.signExtend 64 (holWordExtract 32 31 0 (if rs = 0 then 0 else s.c_gpr s.procID rs)))
  else BitVec.signExtend 128 (if rs = 0 then 0 else s.c_gpr s.procID rs)

/-- Unsigned literal HOL operand of the high-multiply families: the zero
register reads as zero, RV32 zero-extends the low 32 bits, RV64 zero-extends the
full register. -/
private def mulhOpZ (rs : BitVec 5) (s : riscv_state) : BitVec 128 :=
  if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
    BitVec.setWidth 128 (holWordExtract 32 31 0 (if rs = 0 then 0 else s.c_gpr s.procID rs))
  else BitVec.setWidth 128 (if rs = 0 then 0 else s.c_gpr s.procID rs)

/-- Signed literal HOL operand used by `MULHSU`: the low 32 bits are
sign-extended directly into the 128-bit product. -/
private def mulhOpS128 (rs : BitVec 5) (s : riscv_state) : BitVec 128 :=
  if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
    BitVec.signExtend 128 (holWordExtract 32 31 0 (if rs = 0 then 0 else s.c_gpr s.procID rs))
  else BitVec.signExtend 128 (if rs = 0 then 0 else s.c_gpr s.procID rs)

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULH"]
theorem dfnMULH (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'MULH» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0
           then BitVec.signExtend 64 (holWordExtract 32 63 32 (mulhOpS rs1 s * mulhOpS rs2 s))
           else BitVec.signExtend 64 (holWordExtract 64 127 64 (mulhOpS rs1 s * mulhOpS rs2 s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MULH»]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, mulhOpS, GPR, gpr, beq_iff_eq, ne_eq, «write'GPR», «write'gpr»]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULHU"]
theorem dfnMULHU (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'MULHU» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0
           then BitVec.setWidth 64 (holWordExtract 32 63 32 (mulhOpZ rs1 s * mulhOpZ rs2 s))
           else holWordExtract 64 127 64 (mulhOpZ rs1 s * mulhOpZ rs2 s))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MULHU»]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, mulhOpZ, GPR, gpr, beq_iff_eq, ne_eq, «write'GPR», «write'gpr»]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULHSU"]
theorem dfnMULHSU (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'MULHSU» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0
           then BitVec.signExtend 64 (holWordExtract 32 63 32 (mulhOpS128 rs1 s * mulhOpZ rs2 s))
           else holWordExtract 64 127 64 (mulhOpS128 rs1 s * mulhOpZ rs2 s))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MULHSU»]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, mulhOpS128, mulhOpZ, GPR, gpr, beq_iff_eq, ne_eq, «write'GPR», «write'gpr»]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULH_NOP"]
theorem dfnMULHNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'MULH» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'MULH», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULHU_NOP"]
theorem dfnMULHUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'MULHU» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'MULHU», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULHSU_NOP"]
theorem dfnMULHSUNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'MULHSU» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'MULHSU», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, ne_eq]

end Flapjack.RiscV.L3.Step
