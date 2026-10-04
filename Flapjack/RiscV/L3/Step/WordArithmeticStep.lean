import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.WordArithmetic
import Flapjack.RiscV.L3.Defs.UpperJump

/-! Evaluated original `riscv_stepScript.sml` word-arithmetic step theorems
(`Skip` line 637, `ADDIW` line 838, `ADDW` line 859, `SUBW` line 861).  The
three word-arithmetic forms keep the original RV32-exclusion and
invalid-selector mode hypotheses together with the destination hypothesis, and
compute on the low 32 bits before sign-extending the result to 64 bits.  `Skip`
is the unchanged source counter. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Skip"]
theorem dfnSkip (s : riscv_state) : Skip s = s.c_Skip s.procID := rfl

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SUBW"]
theorem dfnSUBW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'SUBW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64
            ((if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) -
              (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'SUBW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;> simp_all [holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADDIW"]
theorem dfnADDIW (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'ADDIW» (rd, (rs1, imm)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if rs1 = 0 then
            BitVec.signExtend 64 (holWordExtract 32 31 0 (BitVec.signExtend 64 imm))
           else
            BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1 + BitVec.signExtend 64 imm)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'ADDIW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> simp_all [holWordExtract]

private theorem addw_low_add_eq (a b : BitVec 64) :
    BitVec.ofNat 32 (a.toNat % 4294967296) + BitVec.ofNat 32 (b.toNat % 4294967296) =
      BitVec.ofNat 32 ((a.toNat + b.toNat) % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADDW"]
theorem dfnADDW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'ADDW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if rs1 = 0 then
            (if rs2 = 0 then 0
             else BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)))
           else if rs2 = 0 then
            BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
           else
            BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1 + s.c_gpr s.procID rs2)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'ADDW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    simp_all [holWordExtract, addw_low_add_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADDW_NOP"]
theorem dfnADDWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'ADDW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'ADDW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SUBW_NOP"]
theorem dfnSUBWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'SUBW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'SUBW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "ADDIW_NOP"]
theorem dfnADDIWNop (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'ADDIW» (rd, (rs1, imm)) s = s := by
  simp only [«dfn'ADDIW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

end Flapjack.RiscV.L3.Step
