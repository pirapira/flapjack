import Flapjack.RiscV.L3.Defs.UpperJump
import Flapjack.RiscV.L3.Step.AvoidSignalAddressException
import Flapjack.RiscV.L3.Step.UpdatePC
import Mathlib.Tactic

/-!
Full evaluated original JAL/JALR equations from riscv_stepScript888-889.
The write theorems retain exactly rd ≠ 0; the generated zero-destination
companions retain exactly rd = 0. A companion suppresses the link-register
write, while preserving the original jump and address-exception effects.
The whole-state normal forms retain the conditional base record and every
original NextFetch/GPR field update, including the source rs1 = 0 branch,
JALR mask, source PC + Skip link and misaligned-fetch path. These equations
are primitive step-library ports, not whole encoder/compiler correctness.
-/

namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3
/-- Original full evaluated JAL write equation, including both address outcomes. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "JAL"]
theorem dfnJal (rd : BitVec 5) (imm : BitVec 20) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'JAL» (rd, imm) s =
    let v : BitVec 64 := s.c_PC s.procID + (BitVec.signExtend 64 imm <<< 1)
    { (if v.getLsbD 0 then signalAddressException (.Fetch_Misaligned, v) s else s) with
      c_NextFetch := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_NextFetch
        else holUpdate s.procID (some (.BranchTo v)) s.c_NextFetch,
      c_gpr := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_gpr
        else holUpdate s.procID (holUpdate rd (s.c_PC s.procID + Skip s) (s.c_gpr s.procID)) s.c_gpr } := by
  simp only [«dfn'JAL», PC, branchTo, «write'NextFetch», «write'GPR», «write'gpr»]
  split <;> simp_all

/-- Original full evaluated JALR write equation; source operands are read before the link write. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "JALR"]
theorem dfnJalr (rd : BitVec 5) (rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd ≠ 0) :
    «dfn'JALR» (rd, rs1, imm) s =
    let v : BitVec 64 := if rs1 = 0 then BitVec.signExtend 64 imm &&& BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE
      else (s.c_gpr s.procID rs1 + BitVec.signExtend 64 imm) &&& BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE
    { (if v.getLsbD 0 then signalAddressException (.Fetch_Misaligned, v) s else s) with
      c_NextFetch := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_NextFetch
        else holUpdate s.procID (some (.BranchTo v)) s.c_NextFetch,
      c_gpr := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_gpr
        else holUpdate s.procID (holUpdate rd (s.c_PC s.procID + Skip s) (s.c_gpr s.procID)) s.c_gpr } := by
  have mask : BitVec.signExtend 64 (BitVec.ofNat 2 2) = BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE := rfl
  simp only [«dfn'JALR», PC, branchTo, «write'NextFetch», «write'GPR», «write'gpr», GPR, gpr, mask]
  split <;> split <;> simp_all

/-- Original zero-destination JAL equation, preserving jump/exception NextFetch effects. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "JAL_NOP"]
theorem dfnJalNop (rd : BitVec 5) (imm : BitVec 20) (s : riscv_state) (h : rd = 0) :
    «dfn'JAL» (rd, imm) s =
    let v : BitVec 64 := s.c_PC s.procID + (BitVec.signExtend 64 imm <<< 1)
    { (if v.getLsbD 0 then signalAddressException (.Fetch_Misaligned, v) s else s) with
      c_NextFetch := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_NextFetch
        else holUpdate s.procID (some (.BranchTo v)) s.c_NextFetch } := by
  simp only [«dfn'JAL», PC, branchTo, «write'NextFetch», «write'GPR», «write'gpr»]
  split <;> simp_all

/-- Original zero-destination JALR equation, preserving jump/exception NextFetch effects. -/
@[hol "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "JALR_NOP"]
theorem dfnJalrNop (rd : BitVec 5) (rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state) (h : rd = 0) :
    «dfn'JALR» (rd, rs1, imm) s =
    let v : BitVec 64 := if rs1 = 0 then BitVec.signExtend 64 imm &&& BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE
      else (s.c_gpr s.procID rs1 + BitVec.signExtend 64 imm) &&& BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE
    { (if v.getLsbD 0 then signalAddressException (.Fetch_Misaligned, v) s else s) with
      c_NextFetch := if v.getLsbD 0 then (signalAddressException (.Fetch_Misaligned, v) s).c_NextFetch
        else holUpdate s.procID (some (.BranchTo v)) s.c_NextFetch } := by
  have mask : BitVec.signExtend 64 (BitVec.ofNat 2 2) = BitVec.ofNat 64 0xFFFFFFFFFFFFFFFE := rfl
  simp only [«dfn'JALR», PC, branchTo, «write'NextFetch», «write'GPR», «write'gpr», GPR, gpr, mask]
  split <;> split <;> simp_all

end Flapjack.RiscV.L3.Step
