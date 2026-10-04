import Flapjack.Compiler.Backend.WordInst
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.WfCutsets

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

/-- Original unconditional label preservation for the entire native optional
three-to-two register pass, including both call-handler families. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_lab_pres" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_labPres {width : Nat} [NeZero width]
    (enabled : Bool) (program : WordLangProgHOL (BitVec width)) :
    extractLabels program = extractLabels (threeToTwoRegProg enabled program) := by
  cases enabled <;> simp [threeToTwoRegProg]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;> simp_all +zetaDelta [extractLabels]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | simp_all +zetaDelta [extractLabels]
        | split
        | constructor
    all_goals
      congr 1 <;> (apply ih; change sizeOf _ < sizeOf _; simp; omega)

/-- Original flat-convention preservation with the source flat-convention
premise, for either setting of the native pass flag and all constructors. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_flatExpConventions {width : Nat} [NeZero width]
    (enabled : Bool) (program : WordLangProgHOL (BitVec width))
    (source : flatExpConventions program = true) :
    flatExpConventions (threeToTwoRegProg enabled program) = true := by
  cases enabled <;> simp [threeToTwoRegProg, source]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;> simp_all +zetaDelta [flatExpConventions]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | exact source.1
        | exact source.2
        | simp_all +zetaDelta [flatExpConventions]
        | split
        | constructor

/-- Original two-register instruction guarantee, with the original enabled
flag premise and no source instruction or target validity assumption. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_two_reg_inst" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_twoRegInst {width : Nat} [NeZero width]
    (enabled : Bool) (program : WordLangProgHOL (BitVec width))
    (runPass : enabled = true) :
    everyInst twoRegInst (threeToTwoRegProg enabled program) = true := by
  cases enabled <;> simp_all [threeToTwoRegProg]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;> simp_all +zetaDelta [everyInst, twoRegInst]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | simp_all +zetaDelta [everyInst]
        | split
        | constructor
    all_goals
      clear ih
      cases program <;> simp_all [everyInst, twoRegInst]
    case ite =>
      rename_i cmp register operand left right notIf
      exact False.elim (notIf cmp register operand left right rfl rfl rfl rfl rfl)

/-- Original full instruction-validity preservation. The configuration is
arbitrary; the sole premise is validity of the source programme. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_fullInstOkLess {width : Nat} [NeZero width]
    (enabled : Bool) (config : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width))
    (source : fullInstOkLessExact config program = true) :
    fullInstOkLessExact config (threeToTwoRegProg enabled program) = true := by
  cases enabled <;> simp [threeToTwoRegProg, source]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;>
      (simp [fullInstOkLessExact, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
         HolRegImm.ofWordRegImm, HolAddr.ofWordLangAddr, instOkLessExact] at ih
       try simp +zetaDelta [fullInstOkLessExact, fullInstOkLessWith,
         HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
         HolAddr.ofWordLangAddr, instOkLessExact] at source
       simp +zetaDelta [*, fullInstOkLessExact, fullInstOkLessWith,
         HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
         HolAddr.ofWordLangAddr, instOkLessExact])
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | exact source.1
        | exact source.2
        | constructor
    case case1 =>
      clear ih
      rename_i operator target originalSource operand
      cases operand <;> simp_all
    case case2 =>
      clear ih
      rename_i operator target originalSource operand
      cases operand <;> simp_all
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | exact source.1
        | exact source.2
        | simp_all +zetaDelta only [fullInstOkLessWith, Bool.and_eq_true]
        | split
        | constructor

/-- Original pre-allocation convention preservation over the faithful native
cut sets and call argument conventions, with the sole source premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_preAllocConventions {width : Nat} [NeZero width]
    (enabled : Bool) (program : WordLangProgHOL (BitVec width))
    (source : preAllocConventionsHOL program = true) :
    preAllocConventionsHOL (threeToTwoRegProg enabled program) = true := by
  cases enabled <;> simp [threeToTwoRegProg, source]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;>
      simp_all +zetaDelta [preAllocConventionsHOL, everyStackVarHOL,
        callArgConventionHOL, instArgConvention]
    case case2 =>
      clear ih
      rename_i operator target originalSource operand
      cases operand <;> simp_all
    all_goals
      repeat' first
        | exact (ih _ (by change sizeOf _ < sizeOf _; simp <;> omega)
            (by simp_all) (by simp_all)).1
        | exact (ih _ (by change sizeOf _ < sizeOf _; simp <;> omega)
            (by simp_all) (by simp_all)).2
        | assumption
        | exact source.1
        | exact source.2
        | split
        | constructor
    all_goals
      simp only [everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true,
        and_true] at source ⊢
    case h_1.left =>
      rename_i _ _ _ _ _ body _ _ _ _ _
      have facts := ih body (by change sizeOf body < sizeOf _; simp; omega)
        source.1.2 source.2.2
      exact ⟨source.1.1, facts.1⟩
    case h_1.right =>
      rename_i _ _ _ _ _ body _ _ _ _ _
      have facts := ih body (by change sizeOf body < sizeOf _; simp; omega)
        source.1.2 source.2.2
      exact ⟨source.2.1, facts.2⟩
    case h_2.left =>
      rename_i _ _ _ _ _ body _ _ _ _ _ handlerBody _ _ _
      have returns := ih body (by change sizeOf body < sizeOf _; simp; omega)
        source.1.1.2 source.2.1.2
      have handler := ih handlerBody
        (by change sizeOf handlerBody < sizeOf _; simp; omega)
        source.1.2 source.2.2.2
      exact ⟨⟨source.1.1.1, returns.1⟩, handler.1⟩
    case h_2.right =>
      rename_i _ _ _ _ _ body _ _ _ _ _ handlerBody _ _ _
      have returns := ih body (by change sizeOf body < sizeOf _; simp; omega)
        source.1.1.2 source.2.1.2
      have handler := ih handlerBody
        (by change sizeOf handlerBody < sizeOf _; simp; omega)
        source.1.2 source.2.2.2
      exact ⟨⟨source.2.1.1, returns.2⟩, ⟨source.2.2.1, handler.2⟩⟩


/-- HOL `three_to_two_reg_prog_wf_cutsets` (`wordConvsProofScript.sml:2227-2236`);
HOL's free flag `b` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem threeToTwoRegProg_wfCutsets {width : Nat} [NeZero width] (b : Bool) :
    ∀ prog : WordLangProgHOL (BitVec width), wfCutsets prog → wfCutsets (threeToTwoRegProg b prog) := by
  intro program source
  cases b <;> simp [threeToTwoRegProg, source]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;> simp_all +zetaDelta [wfCutsets]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta [wfCutsets]
        | split
        | constructor

end Flapjack.WordConvs
