import Flapjack.RiscV.L3.Defs.IntegerLoad
import Flapjack.Misc.Alignment
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-! Evaluated original `riscv_stepScript.sml` memory-load instruction theorems
(`LD`/`LW`/`LH`/`LB`/`LWU`/`LHU`/`LBU`, lines 902-908) over the literal native
equations, together with their generated `rd = 0` companions.  Each theorem
keeps the original hypotheses: the destination guard `rd <> 0`, the bare-mode
guard `mstatus.VM = 0`, the source-alignment premise `aligned` (present on the
write theorems `LD`/`LW`/`LH`/`LWU`/`LHU` and on `LD_NOP`), rendered as the
tagged `Flapjack.holAligned p addr = true`, and, for the
64-bit-capable loads `LD`/`LWU`, the architecture guards `ArchBase <> 0`/
`ArchBase <> 1`.  Address computation, sign/zero extension, the mode guard
ordering, and the whole-state record update follow the original clauses
exactly. -/

/-- Bare-memory translation: under `mstatus.VM = 0` the original `translateAddr`
returns the unpaged address.  Flapjack-only helper (no separate HOL theorem). -/
theorem translateAddr_bare (vAddr : BitVec 64) (ft : fetchType) (ac : accessType) (s : riscv_state)
    (h : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    translateAddr (vAddr, (ft, ac)) s = (some vAddr, s) := by
  simp [translateAddr, vmType, MCSR, h]

/-- The original 64-bit loads exclude the 32-bit architecture: for
`ArchBase` outside `{0,1}` the mode test is false and returns the state
unchanged.  Flapjack-only helper. -/
theorem in32BitMode_false (s : riscv_state)
    (h0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (h1 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) :
    in32BitMode () s = (false, s) := by
  simp only [in32BitMode, curArch, architecture, MCSR]
  have hcases : ∀ b : BitVec 2, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by decide
  rcases hcases (s.c_MCSR s.procID).mcpuid.ArchBase with h | h | h | h <;>
    simp_all

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LD"]
theorem dfnLD (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LD» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
            else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LD»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LW"]
theorem dfnLW (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd ≠ 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LW» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64 (holWordExtract 32 31 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LW»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LH"]
theorem dfnLH (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd ≠ 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LH» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64 (holWordExtract 16 15 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LH»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LB"]
theorem dfnLB (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd ≠ 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LB» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.signExtend 64 (holWordExtract 8 7 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LB»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LWU"]
theorem dfnLWU (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd ≠ 0)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LWU» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.setWidth 64 (holWordExtract 32 31 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LWU»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LHU"]
theorem dfnLHU (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd ≠ 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LHU» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.setWidth 64 (holWordExtract 16 15 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LHU»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LD_NOP"]
theorem dfnLDNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (_haligned : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true) :
    «dfn'LD» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LD»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LW_NOP"]
theorem dfnLWNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd = 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LW» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LW»]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LH_NOP"]
theorem dfnLHNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd = 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LH» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LH»]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LB_NOP"]
theorem dfnLBNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd = 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LB» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LB»]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LWU_NOP"]
theorem dfnLWUNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (harch0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0)
    (harch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1) (hrd : rd = 0)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LWU» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LWU»]
  rw [in32BitMode_false s harch0 harch]
  simp only [Bool.false_eq_true, reduceIte]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LHU_NOP"]
theorem dfnLHUNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd = 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LHU» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LHU»]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LBU"]
theorem dfnLBU (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd ≠ 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LBU» (rd, (rs1, offs)) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd
          (BitVec.setWidth 64 (holWordExtract 8 7 0
            (rawReadData (if rs1 = 0 then BitVec.signExtend 64 offs
              else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) s)))
          (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'LBU»]
  have hv : GPR rs1 s + BitVec.signExtend 64 offs =
      (if rs1 = 0 then BitVec.signExtend 64 offs
       else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) := by
    by_cases hr1 : rs1 = 0 <;> simp_all [GPR, gpr]
  rw [hv, translateAddr_bare _ _ _ s hVM]
  simp only [«write'GPR», «write'gpr»]
  rw [if_pos (by simpa [beq_iff_eq] using hrd)]

@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "LBU_NOP"]
theorem dfnLBUNop (rd rs1 : BitVec 5) (offs : BitVec 12) (s : riscv_state)
    (hrd : rd = 0) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'LBU» (rd, (rs1, offs)) s = s := by
  simp only [«dfn'LBU»]
  rw [translateAddr_bare _ _ _ s hVM]
  simp [«write'GPR», hrd]

end Flapjack.RiscV.L3.Step
