import Mathlib.Tactic.IntervalCases
import Flapjack.Misc.Alignment
import Flapjack.Compiler.Encoders.RiscV.Target
import Flapjack.RiscV.L3.Defs.Run

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem high_eq (c : BitVec 32) :
    RiscV.L3.holWordExtract 20 31 12 c = c.extractLsb' 12 20 := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem low_eq (c : BitVec 32) :
    RiscV.L3.holWordExtract 12 11 0 c = c.extractLsb' 0 12 := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem xor_reconstruct (c : BitVec 32) (bit : c.getLsbD 11 = true) :
    ((~~~(c.extractLsb' 12 20) ++ 0#12).signExtend 64) ^^^
      ((c.extractLsb' 0 12).signExtend 64) = c.signExtend 64 := by
  have hbit : c[11] = true := by simpa using bit
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_signExtend,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append, BitVec.getLsbD_not,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp [hbit]

private theorem add_reconstruct (c : BitVec 32) (bit : c.getLsbD 11 = false) :
    ((c.extractLsb' 12 20 ++ 0#12).signExtend 64) +
      ((c.extractLsb' 0 12).signExtend 64) = c.signExtend 64 := by
  have lo : (c.extractLsb' 0 12).msb = false := by
    simpa [BitVec.msb_eq_getLsbD_last] using bit
  have split : c.extractLsb' 12 20 ++ c.extractLsb' 0 12 = c :=
    BitVec.extractLsb'_append_extractLsb'
  have integer := congrArg BitVec.toInt split
  simp only [BitVec.toInt_append, beq_iff_eq, Nat.reduceEqDiff, ite_false] at integer
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add]
  simp only [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64),
    BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64),
    BitVec.toInt_append_zero, BitVec.toInt_eq_toNat_of_msb lo]
  rw [integer]
  have lower := BitVec.le_toInt c
  have upper := BitVec.toInt_lt (x := c)
  apply (Int.bmod_eq_iff (by decide : 0 < 2 ^ 64)).mpr
  constructor
  · norm_num at lower ⊢
    omega
  · constructor
    · norm_num at upper ⊢
      omega
    · simp

/-- Native value reconstruction for both literal riscvConst32 branches.
This composition identity has no separately named HOL original; it is untagged
infrastructure for the full original Const execution proof. Every intrinsic
word32 value is retained, without range or target-evaluation premises. -/
theorem const32_value_reconstruction (c : BitVec 32) :
    (if c.getLsbD 11 then
      ((~~~(RiscV.L3.holWordExtract 20 31 12 c) ++ 0#12).signExtend 64) ^^^
        ((RiscV.L3.holWordExtract 12 11 0 c).signExtend 64)
     else
      ((RiscV.L3.holWordExtract 20 31 12 c ++ 0#12).signExtend 64) +
        ((RiscV.L3.holWordExtract 12 11 0 c).signExtend 64)) = c.signExtend 64 := by
  rw [high_eq, low_eq]
  cases bit : c.getLsbD 11
  · simp only [Bool.false_eq_true, ite_false]
    exact add_reconstruct c bit
  · simp only [ite_true]
    exact xor_reconstruct c bit

private theorem update_overwrite {α β : Type} [DecidableEq α]
    (a : α) (v u : β) (f : α → β) :
    holUpdate a v (holUpdate a u f) = holUpdate a v f := by
  funext x
  by_cases h : a = x <;> simp [holUpdate, h]

/-- Actual local native Run composition of the two original Const32
instructions, for every state and intrinsic destination (including zero).
There is no separately named HOL composition theorem. This untagged helper
does not replace the full fetch/Next/interference encoder theorem. -/
theorem run_const32 (rd : BitVec 5) (c : BitVec 32) (ms : riscv_state) :
    (Compiler.Encoders.RiscV.Target.riscvConst32 rd c).foldl
      (fun s i => Run i s) ms = «write'GPR» (c.signExtend 64,rd) ms := by
  have value := const32_value_reconstruction c
  cases bit : c.getLsbD 11 <;>
    simp only [bit, Bool.false_eq_true, ite_false, ite_true] at value
  all_goals
    simp only [Compiler.Encoders.RiscV.Target.riscvConst32, bit,
      Bool.false_eq_true, ite_false, ite_true, List.foldl_cons, List.foldl_nil,
      Run, «dfn'LUI», «dfn'XORI», «dfn'ADDI», BitVec.setWidth_eq]
    by_cases zero : rd = 0#5
    · subst rd
      simp [«write'GPR»]
    · simp [«write'GPR», «write'gpr», GPR, gpr, holUpdate, zero]
      rw [value]
      simp only [update_overwrite]

end Flapjack.RiscV.TargetProof
