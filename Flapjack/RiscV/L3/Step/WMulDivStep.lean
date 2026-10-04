import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.Divide

/-! Evaluated original `riscv_stepScript.sml` W-multiply/divide step theorems
(`MULW`/`DIVW`/`DIVUW`/`REMW`/`REMUW`, lines 874-886).  Each keeps the original
RV32-exclusion and invalid-selector mode hypotheses together with the
destination hypothesis, signals `Illegal_Instr` on RV32, and computes on the low
32 bits before sign-extending the result.  The generated `rd = 0w` companions
retain the mode hypotheses. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULW"]
theorem dfnMULW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'MULW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64 (holWordExtract 32 31 0 (BitVec.signExtend 64
            ((if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1)) *
             (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MULW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;> simp_all [holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DIVW"]
theorem dfnDIVW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'DIVW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else holWordExtract 32 31 0 (s.c_gpr s.procID rs2) = 0)
           then BitVec.signExtend 64 (BitVec.ofNat 1 1)
           else BitVec.signExtend 64 (BitVec.sdiv
            (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
            (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'DIVW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)) = 0 <;>
    simp_all [beq_iff_eq, holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DIVUW"]
theorem dfnDIVUW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'DIVUW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else holWordExtract 32 31 0 (s.c_gpr s.procID rs2) = 0)
           then BitVec.signExtend 64 (BitVec.ofNat 1 1)
           else BitVec.signExtend 64 (BitVec.udiv
            (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
            (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'DIVUW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)) = 0 <;>
    simp_all [beq_iff_eq, holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REMW"]
theorem dfnREMW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'REMW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else holWordExtract 32 31 0 (s.c_gpr s.procID rs2) = 0)
           then (if rs1 = 0 then 0
            else BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)))
           else BitVec.signExtend 64 (BitVec.srem
            (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
            (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REMW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)) = 0 <;>
    simp_all [beq_iff_eq, holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REMUW"]
theorem dfnREMUW (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0) :
    «dfn'REMUW» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else holWordExtract 32 31 0 (s.c_gpr s.procID rs2) = 0)
           then (if rs1 = 0 then 0
            else BitVec.signExtend 64 (holWordExtract 32 31 0 (s.c_gpr s.procID rs1)))
           else BitVec.signExtend 64 (BitVec.umod
            (if rs1 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs1))
            (if rs2 = 0 then 0 else holWordExtract 32 31 0 (s.c_gpr s.procID rs2))))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REMUW»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte, «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : (holWordExtract 32 31 0 (s.c_gpr s.procID rs2)) = 0 <;>
    simp_all [beq_iff_eq, holWordExtract]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MULW_NOP"]
theorem dfnMULWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'MULW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'MULW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DIVW_NOP"]
theorem dfnDIVWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'DIVW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'DIVW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DIVUW_NOP"]
theorem dfnDIVUWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'DIVUW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'DIVUW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REMW_NOP"]
theorem dfnREMWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'REMW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'REMW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REMUW_NOP"]
theorem dfnREMUWNop (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0) :
    «dfn'REMUW» (rd, (rs1, rs2)) s = s := by
  simp only [«dfn'REMUW», «write'GPR», hrd]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all [in32BitMode, curArch, architecture, MCSR, beq_iff_eq, ne_eq]

end Flapjack.RiscV.L3.Step
