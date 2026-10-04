import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.Divide

/-! Evaluated original `riscv_stepScript.sml` integer multiply/divide instruction
theorems for four full-width forms (`MUL`, `DIV`, `REM`, `REMU`, lines
874-886) over the literal native equations and the hex-equivalent all-ones
zero-divisor result.  Each write theorem keeps the original destination
hypothesis `rd <> 0w`; the remainder/quotient forms preserve the explicit zero
divisor branches. The evaluated `DIVU` and word-form equations remain separate
porting work; this module does not claim those results. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "MUL"]
theorem dfnMUL (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'MUL» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          ((if rs1 = 0 then 0 else s.c_gpr s.procID rs1) *
           (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'MUL», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DIV"]
theorem dfnDIV (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'DIV» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then BitVec.signExtend 64 (BitVec.ofNat 1 1)
           else BitVec.sdiv (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'DIV», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REM"]
theorem dfnREM (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'REM» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
           else BitVec.srem (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REM», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "REMU"]
theorem dfnREMU (rd rs1 rs2 : BitVec 5) (s : riscv_state) (hrd : rd ≠ 0) :
    «dfn'REMU» (rd, (rs1, rs2)) s =
      { s with
        c_gpr := holUpdate s.procID (holUpdate rd
          (if (if rs2 = 0 then True else s.c_gpr s.procID rs2 = 0)
           then (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
           else BitVec.umod (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)
             (if rs2 = 0 then 0 else s.c_gpr s.procID rs2))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'REMU», «write'GPR», «write'gpr», GPR, gpr]
  by_cases h1 : rs1 = 0 <;> by_cases h2 : rs2 = 0 <;>
    by_cases hz : s.c_gpr s.procID rs2 = 0 <;> simp_all [beq_iff_eq]

end Flapjack.RiscV.L3.Step
