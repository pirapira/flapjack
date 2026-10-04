import Flapjack.RiscV.CorrectnessEncoding.ConstExecution

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Literal native PC/Skip fields of a nonempty Const instruction list.
Untagged state-update infrastructure with no separately named HOL declaration. -/
def constControls (ms : riscv_state) (pc : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_PC := holUpdate ms.procID pc ms.c_PC}

/-- The literal seven register Run clauses do not observe PC or Skip. The
native RV64 mode follows from original riscv_ok; arbitrary new PC is allowed
because this is a Run equation, not a Next-validity assertion. -/
theorem const_run_controls (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (pc : BitVec 64) (ok : riscvOk ms = true) :
    Run i (constControls ms pc) = constControls (Run i ms) pc := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases kind
  all_goals
    simp [Run, «dfn'LUI», «dfn'ADDI», «dfn'ORI», «dfn'XORI», «dfn'SLLI»,
      «dfn'OR», «dfn'XOR», in32BitMode, curArch, architecture, MCSR, arch,
      «write'GPR», «write'gpr», constControls, GPR, gpr]
    split_ifs <;> rfl

/-- Whole original register Run lists commute with the native control fields.
All intrinsic operands and list lengths are retained. Untagged infrastructure. -/
theorem const_run_list_controls (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i)
    (ms : riscv_state) (pc : BitVec 64) (ok : riscvOk ms = true) :
    is.foldl (fun s i => Run i s) (constControls ms pc) =
      constControls (is.foldl (fun s i => Run i s) ms) pc := by
  induction is generalizing ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    simp only [List.foldl_cons]
    rw [const_run_controls i kind ms pc ok]
    exact ih (fun j hj => kinds j (List.mem_cons_of_mem i hj))
      (Run i ms) (const_run_ok i kind ms ok)

/-- Complete pure native step is precisely register Run followed by the
literal original Skip4/PC4 control update. -/
theorem const_step_controls (i : instruction) (kind : ConstRegisterInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    constStep i ms = constControls (Run i ms) (ms.c_PC ms.procID + 4) := by
  have frame := const_run_frame i kind ms ok
  simp [constStep, constControls, frame.1]

private theorem controls_overwrite (ms : riscv_state) (pc1 pc2 : BitVec 64) :
    constControls (constControls ms pc1) pc2 = constControls ms pc2 := by
  simp only [constControls]
  congr 1 <;> funext core <;> by_cases eq : ms.procID = core <;> simp [holUpdate,eq]

/-- Complete native step fold differs from the original register Run fold
only by the literal current-core PC/Skip fields. Empty lists leave the entire
state unchanged; every nonempty list sets Skip4 and advances PC4 per instruction.
All intrinsic operands and list lengths are retained, with original validity
only. Untagged composition infrastructure for full Const final-state assembly. -/
theorem const_step_list_controls (is : List instruction)
    (kinds : ∀ i ∈ is, ConstRegisterInstruction i) (ms : riscv_state)
    (ok : riscvOk ms = true) :
    is.foldl (fun s i => constStep i s) ms =
      if is = [] then ms else
        constControls (is.foldl (fun s i => Run i s) ms)
          (ms.c_PC ms.procID + BitVec.ofNat 64 (4 * is.length)) := by
  induction is generalizing ms with
  | nil => rfl
  | cons i is ih =>
    have kind := kinds i (by simp)
    have tailKinds : ∀ j ∈ is, ConstRegisterInstruction j :=
      fun j hj => kinds j (List.mem_cons_of_mem i hj)
    have runOk := const_run_ok i kind ms ok
    have stepOk := const_step_ok i kind ms ok
    have frame := const_step_frame i kind ms ok
    simp only [List.foldl_cons]
    rw [ih tailKinds (constStep i ms) stepOk]
    by_cases empty : is = []
    · subst is
      simpa using const_step_controls i kind ms ok
    · simp only [if_neg empty, List.cons_ne_nil, if_false, List.length_cons]
      rw [frame.1, frame.2.2, const_step_controls i kind ms ok,
        const_run_list_controls is tailKinds (Run i ms) _ runOk, controls_overwrite]
      congr 1
      simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
      change ms.c_PC ms.procID + 4 + BitVec.ofNat 64 (4 * is.length) =
        ms.c_PC ms.procID + (BitVec.ofNat 64 (4 * is.length) + 4)
      rw [BitVec.add_assoc, BitVec.add_comm (4 : BitVec 64) (BitVec.ofNat 64 (4 * is.length))]

/-- Every literal Const32 lowering member belongs to the full seven-family
native register instruction carrier. No constant or destination restriction. -/
theorem const32_register_family (r : BitVec 5) (c : BitVec 32) :
    ∀ i ∈ riscvConst32 r c, ConstRegisterInstruction i := by
  simp only [riscvConst32]
  split
  all_goals
    intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor

/-- Every literal full Const lowering member belongs to the seven native
families, for every source Nat destination and word64 constant. -/
theorem const_register_family (r : Nat) (c : BitVec 64) :
    ∀ i ∈ riscvAst (.inst (.const r c)), ConstRegisterInstruction i := by
  simp only [riscvAst]
  split
  · intro i member
    simp only [List.mem_singleton] at member
    subst i
    constructor
  · split
    · exact const32_register_family _ _
    · split
      all_goals
        intro i member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (member | member) | (rfl | rfl)
        · exact const32_register_family _ _ i member
        · exact const32_register_family _ _ i member
        · constructor
        · constructor

/-- Full Const lowering always emits a nonempty native instruction list.
This derives the nonempty control update rather than assuming a target run. -/
theorem const_register_nonempty (r : Nat) (c : BitVec 64) :
    riscvAst (.inst (.const r c)) ≠ [] := by
  simp only [riscvAst]
  split
  · simp
  · split
    · simp only [riscvConst32]
      split <;> simp
    · split
      all_goals
        simp only [riscvConst32]
        split <;> simp

/-- Complete native Const post-state, derived from original asm_ok and
riscv_ok only. The accepted Run result supplies the exact constant and
wide-path scratch31 value; the complete step fold supplies Skip4 and PC advance.
Untagged composition infrastructure; full original assertions remain open. -/
theorem const_step_post (r : Nat) (c : BitVec 64) (ms : riscv_state)
    (ok : Compiler.Encoders.Asm.asmOkExact (.inst (.const r c)) riscvConfig = true)
    (state : riscvOk ms = true) :
    (riscvAst (.inst (.const r c))).foldl (fun s i => constStep i s) ms =
      constControls (constRunPost r c ms)
        (ms.c_PC ms.procID + BitVec.ofNat 64 (4 * (riscvAst (.inst (.const r c))).length)) := by
  rw [const_step_list_controls _ (const_register_family r c) ms state,
    if_neg (const_register_nonempty r c), run_const r c ms ok state]

end Flapjack.RiscV.TargetProof
