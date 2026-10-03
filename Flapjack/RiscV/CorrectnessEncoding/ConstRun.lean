import Flapjack.RiscV.CorrectnessEncoding.Const32
import Flapjack.RiscV.CorrectnessEncoding.ConstWide
import Flapjack.Compiler.Encoders.RiscV.Target.State

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem update_overwrite {α β : Type} [DecidableEq α]
    (a : α) (v u : β) (f : α → β) :
    holUpdate a v (holUpdate a u f) = holUpdate a v f := by
  funext x
  by_cases h : a = x <;> simp [holUpdate, h]

private theorem high_eq (c : BitVec 64) :
    holWordExtract 32 63 32 c = c.extractLsb' 32 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb'_toNat]
private theorem low_eq (c : BitVec 64) :
    holWordExtract 32 31 0 c = c.extractLsb' 0 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.extractLsb'_toNat]

private def is32 (c : BitVec 64) : Bool :=
    (holWordExtract 32 63 32 c == 0 && !c.getLsbD 31) ||
      (holWordExtract 32 63 32 c == -1 && c.getLsbD 31)
private theorem reconstruct32 (c : BitVec 64) (h : is32 c = true) :
    (holWordExtract 32 31 0 c).signExtend 64 = c := by
  have value := const_wide_value_reconstruction c
  simp only [is32, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    ] at h
  rcases h with h | h
  · have high : c.extractLsb' 32 32 = 0 := by simpa [high_eq] using h.1
    have bit : c[31] = false := by simpa using h.2
    simpa [bit, high, low_eq] using value
  · have high : c.extractLsb' 32 32 = -1 := by simpa [high_eq] using h.1
    simpa [h.2, high, low_eq] using value

/-- Exact complete native state after local Const lowering. Scratch31 is
changed only by the literal wide path, retaining its sign-extended low32. -/
def constRunPost (r : Nat) (c : BitVec 64) (ms : riscv_state) : riscv_state :=
  let low12 := holWordExtract 12 11 0 c
  let input := if c == low12.signExtend 64 || is32 c then ms
    else «write'GPR» ((holWordExtract 32 31 0 c).signExtend 64,31) ms
  «write'GPR» (c,BitVec.ofNat 5 r) input

/-- Flapjack infrastructure for every original Const lowering branch. The
original asm_ok and riscv_ok restrictions are the only guards: both follow
from the full encoder theorem's source step/state relation. No target run or
narrowed constant range is assumed; this is not yet the full fetch theorem. -/
theorem run_const (r : Nat) (c : BitVec 64) (ms : riscv_state)
    (ok : asmOkExact (.inst (.const r c)) riscvConfig = true)
    (state : riscvOk ms = true) :
    (riscvAst (.inst (.const r c))).foldl (fun s i => Run i s) ms =
      constRunPost r c ms := by
  have guard : r < 32 ∧ r ≠ 0 ∧ r ≠ 31 := by
    have g := ok
    simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true] at g
    have avoid := g.2
    simp [riscvConfig] at avoid
    exact ⟨of_decide_eq_true g.1, avoid.1, avoid.2.2.2.2⟩
  have arch := ((riscvOk_iff ms).mp state).2.1
  have nz : BitVec.ofNat 5 r ≠ 0#5 := by
    intro h
    have n := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt guard.1] at n
    exact guard.2.1 n
  have scratch : BitVec.ofNat 5 r ≠ 31#5 := by
    intro h
    have n := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt guard.1] at n
    exact guard.2.2 n
  simp only [riscvAst]
  split
  · rename_i small
    have value : c = (holWordExtract 12 11 0 c).signExtend 64 := by simpa using small
    simp only [constRunPost, small, Bool.true_or, ite_true]
    simp only [List.foldl_cons, List.foldl_nil, Run, «dfn'ORI»]
    simp only [GPR, gpr, BitVec.ofNat_eq_ofNat]
    rw [← value]
    simp
  · rename_i small
    split
    · rename_i medium
      rw [run_const32, reconstruct32 c medium]
      have hm : is32 c = true := medium
      simp only [constRunPost, small, hm, Bool.or_true, ite_true]
    · rename_i medium
      split
      all_goals
        rename_i bit
        rw [List.foldl_append, List.foldl_append, run_const32, run_const32]
        simp only [List.foldl_cons, List.foldl_nil, Run, «dfn'SLLI», «dfn'XOR», «dfn'OR»]
        have value := const_wide_value_reconstruction c
        simp only [bit, Bool.false_eq_true, ite_false, ite_true] at value
        rw [← high_eq, ← low_eq] at value
        have hm : is32 c = false := Bool.eq_false_iff.mpr medium
        simp only [constRunPost, small, hm, Bool.false_or]
        simp [in32BitMode, curArch, architecture, MCSR, «write'GPR»,
          «write'gpr», GPR, gpr, holUpdate, nz, scratch, arch]
        try simp only [BitVec.signExtend_not (by decide : 0 < 32)] at value
        rw [value]
        simp only [update_overwrite]

end Flapjack.RiscV.TargetProof
