import Flapjack.RiscV.CorrectnessEncoding.ConstPost
import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.Compiler.Encoders.AsmSem.Step

namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Literal source Const post-state from original asm_step, including exactly
its encoded byte length. Untagged specialization infrastructure. -/
theorem const_source_post (r : Nat) (c : BitVec 64) (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.inst (.const r c)) s2) :
    s2 = updPc (s1.pc + BitVec.ofNat 64
      (4 * (riscvAst (.inst (.const r c))).length)) (updReg r c s1) := by
  have step := h.2.2.2.2.1
  simpa only [asmUpd, instUpd, riscvConfig, riscvEnc_length_eq] using step.symm

/-- Final source/native relation of the complete pure Const list. The only
premises are the original source step and initial target state relation.
Scratch31 is retained in the native state and excluded only by original avoidRegs.
Untagged assembly infrastructure; full interference assertions remain open. -/
theorem const_step_post_relation (r : Nat) (c : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvConfig s1 (.inst (.const r c)) s2)
    (rel : targetStateRel riscvTarget s1 ms) :
    targetStateRel riscvTarget s2
      ((riscvAst (.inst (.const r c))).foldl (fun s i => constStep i s) ms) := by
  have ok := h.2.2.2.2.2.2
  have guard : r < 32 ∧ r ≠ 0 := by
    have g := ok
    simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true] at g
    have avoid := g.2
    simp [riscvConfig] at avoid
    exact ⟨of_decide_eq_true g.1, avoid.1⟩
  have rn : BitVec.ofNat 5 r ≠ 0#5 := by
    intro e
    have n := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt guard.1] at n
    exact guard.2 n
  have frame := const_step_list_frame _ (const_register_family r c) ms rel.1
  dsimp only at frame
  let final := (riscvAst (.inst (.const r c))).foldl (fun s i => constStep i s) ms
  rw [const_source_post r c s1 s2 h]
  refine ⟨frame.1, ?_, ?_, ?_, ?_⟩
  · change final.c_PC final.procID = s1.pc + _
    rw [frame.2.2.2]
    exact congrArg (fun pc => pc + BitVec.ofNat 64
      (4 * (riscvAst (.inst (.const r c))).length)) rel.2.1
  · intro a domain
    change final.MEM8 a = s1.mem a
    rw [frame.2.2.1]
    exact rel.2.2.1 a domain
  · intro i hi
    have ibound : i < 32 := hi.1
    have avoid := hi.2
    change [0,2,3,4,31].contains i = false at avoid
    simp at avoid
    have inz : BitVec.ofNat 5 i ≠ 0#5 := by
      intro e
      have n := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at n
      norm_num at n
      rw [Nat.mod_eq_of_lt ibound] at n
      exact avoid.1 n
    have scratch : (31#5) ≠ BitVec.ofNat 5 i := by
      intro e
      have n := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at n
      norm_num at n
      rw [Nat.mod_eq_of_lt ibound] at n
      exact avoid.2.2.2.2 n.symm
    have before := rel.2.2.2.1 i hi
    change ms.c_gpr ms.procID (BitVec.ofNat 5 i) = s1.regs i at before
    change final.c_gpr final.procID (BitVec.ofNat 5 i) = if i = r then c else s1.regs i
    dsimp only [final]
    rw [const_step_post r c ms ok rel.1]
    by_cases eq : i = r
    · subst i
      simp only [constRunPost]
      split_ifs
      all_goals simp [constControls, «write'GPR», «write'gpr», rn, holUpdate]
    · have ne : BitVec.ofNat 5 r ≠ BitVec.ofNat 5 i := by
        intro e
        have n := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at n
        norm_num at n
        rw [Nat.mod_eq_of_lt guard.1, Nat.mod_eq_of_lt ibound] at n
        exact eq n.symm
      simp only [constRunPost]
      split_ifs
      all_goals simp_all [constControls, «write'GPR», «write'gpr», holUpdate]
  · intro i hi
    change i < 0 at hi
    omega

end Flapjack.RiscV.TargetProof
