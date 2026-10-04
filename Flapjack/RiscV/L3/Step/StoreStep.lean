import Flapjack.RiscV.L3.Step.LoadStep
import Flapjack.RiscV.L3.Defs.IntegerStore

/-! Evaluated original `riscv_stepScript.sml` memory-store instruction theorems
(`SD`/`SW`/`SH`/`SB`, lines 908-915) over the literal native `dfn'SD`/`dfn'SW`/
`dfn'SH`/`dfn'SB` equations.  Each write theorem keeps the original source
hypotheses captured from `riscv_stepTheory`: `mstatus.VM = 0w` for every store,
plus the RV32-exclusion `ArchBase <> 0w` for `SD`, plus the source `aligned`
condition (`SD` 3 bits, `SW` 2 bits, `SH` 1 bit).  `SB` has no alignment
condition.  The store factory is a plain `class` (not `class_rd0`), so no
generated `rd = 0w` companions exist.  The right-hand sides state the
definitionally-equal `rawWriteData` form of the original expanded `MEM8`
updates; no original branch, value or address is altered. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SD"]
theorem dfnSD (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SD» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 8) s := by
  simp only [«dfn'SD»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SW"]
theorem dfnSW (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SW» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 4) s := by
  simp only [«dfn'SW»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SH"]
theorem dfnSH (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'SH» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 2) s := by
  simp only [«dfn'SH»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "SB"]
theorem dfnSB (rs1 rs2 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'SB» (rs1, rs2, offs) s =
      rawWriteData ((if rs1 = 0 then BitVec.signExtend 64 offs
        else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs), GPR rs2 s, 1) s := by
  simp only [«dfn'SB»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]

end Flapjack.RiscV.L3.Step
