import Flapjack.RiscV.CorrectnessEncoding.BinopRun
import Flapjack.Compiler.Encoders.RiscV.Target.State

/-! Local source/Run compositions required by the full original Shift encoder
case560-620. They have no separately named HOL originals and remain untagged
infrastructure. Source results cover all four operators and both RegImm forms
from asmStep alone. Native Run equations use the original riscvOk restriction
of the fixed RV64 target, not an extra premise for the eventual encoder port.
Every intrinsic register/count and literal low6 register mask is retained. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Literal source Shift count assertion, factored only for this local proof.
No separately named HOL declaration exists for this fixed-width composition. -/
def shiftSourceCountOk (right : HolRegImm 64) (s : AsmState 64) : Bool :=
  match right with
  | .reg r => decide ((readReg r s).toNat < 64)
  | .imm _ => true

/-- Original source register-count assertion follows from successful asmStep.
No independent named HOL declaration states this local consequence. -/
theorem shift_source_count (op : Flapjack.Shift) (rd rs : Nat) (right : HolRegImm 64)
    (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.inst (.arith (.shift op rd rs right))) s2) :
    shiftSourceCountOk right s1 = true := by
  cases right with
  | imm c => rfl
  | reg r =>
    change decide ((readReg r s1).toNat < 64) = true
    cases valid : decide ((readReg r s1).toNat < 64) with
    | false =>
      have failed := h.2.2.2.2.2.1
      rw [← h.2.2.2.2.1] at failed
      simp [asmUpd, instUpd, arithUpd, assertState, updPc, updReg, valid] at failed
    | true => rfl

/-- Whole original source post-state for every Shift operator and operand form,
including both rotate paths and their actual emitted-byte lengths. Untagged
local composition, with no range or target-run premise. -/
theorem shift_source_post (op : Flapjack.Shift) (rd rs : Nat) (right : HolRegImm 64)
    (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.inst (.arith (.shift op rd rs right))) s2) :
    s2 = updPc (s1.pc + BitVec.ofNat 64
      (riscvConfig.encode (.inst (.arith (.shift op rd rs right)))).length)
      (updReg rd (wordShift op (readReg rs s1) (regImm right s1).toNat) s1) := by
  have update := h.2.2.2.2.1.symm
  have count := shift_source_count op rd rs right s1 s2 h
  cases right with
  | reg r =>
    simp only [asmUpd, instUpd, arithUpd] at update
    simp only [shiftSourceCountOk] at count
    rw [count] at update
    simpa [assertState] using update
  | imm c =>
    simpa [asmUpd, instUpd, arithUpd, assertState] using update

/-- Actual SLL Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_sll (rd rs1 : BitVec 5) (rs2 : BitVec 5)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SLL (rd, rs1, rs2))) ms =
      «write'GPR» ((GPR rs1 ms) <<< (((RiscV.L3.holWordExtract 6 5 0 (GPR rs2 ms)).setWidth 64).toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SLL», in32BitMode, curArch, architecture, MCSR, arch]

/-- Actual SLLI Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_slli (rd rs1 : BitVec 5) (amount : BitVec 6)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SLLI (rd, rs1, amount))) ms =
      «write'GPR» ((GPR rs1 ms) <<< (amount.toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SLLI», in32BitMode, curArch, architecture, MCSR, arch]

/-- Actual SRL Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_srl (rd rs1 : BitVec 5) (rs2 : BitVec 5)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SRL (rd, rs1, rs2))) ms =
      «write'GPR» ((GPR rs1 ms) >>> (((RiscV.L3.holWordExtract 6 5 0 (GPR rs2 ms)).setWidth 64).toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SRL», in32BitMode, curArch, architecture, MCSR, arch]

/-- Actual SRLI Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_srli (rd rs1 : BitVec 5) (amount : BitVec 6)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SRLI (rd, rs1, amount))) ms =
      «write'GPR» ((GPR rs1 ms) >>> (amount.toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SRLI», in32BitMode, curArch, architecture, MCSR, arch]

/-- Actual SRA Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_sra (rd rs1 : BitVec 5) (rs2 : BitVec 5)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SRA (rd, rs1, rs2))) ms =
      «write'GPR» ((GPR rs1 ms).sshiftRight (((RiscV.L3.holWordExtract 6 5 0 (GPR rs2 ms)).setWidth 64).toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SRA», in32BitMode, curArch, architecture, MCSR, arch]

/-- Actual SRAI Run composition under the original fixed-target riscvOk
restriction. Untagged infrastructure; all intrinsic operands remain arbitrary. -/
theorem shift_run_srai (rd rs1 : BitVec 5) (amount : BitVec 6)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Shift (.SRAI (rd, rs1, amount))) ms =
      «write'GPR» ((GPR rs1 ms).sshiftRight (amount.toNat), rd) ms := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp [Run, «dfn'SRAI», in32BitMode, curArch, architecture, MCSR, arch]

end Flapjack.RiscV.TargetProof
