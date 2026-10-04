import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Compiler.Backend.WordInst
import Flapjack.Pancake.Proofs.WordConvs.InstSelectExp
import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram
import Flapjack.Pancake.WordConvs.NotCreated

/-!
# `wordConvsProof`: `not_created_subprogs` through the `word_to_word` passes

The `not_created_subprogs` preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` for the passes of
`compile_single`: the `word_simp` group (516-628), `inst_select` (884-902), the
SSA group (1128-1225), `three_to_two_reg_prog` (2204-2213) and `remove_unreach`
(2402-2434), and `compile_single_not_created_subprogs` (2972-2989). HOL's free
predicate `P` is the leading binder throughout; HOL's Boolean `=`/`∧` on
`not_created_subprogs` are Lean `Bool` `=`/`&&`.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordSimp

section WordSimp

variable {width : Nat} [NeZero width]

/-- HOL `not_created_subprogs_SmartSeq` (`wordConvsProofScript.sml:516-521`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_SmartSeq"
  (words_as_type_indexed_bitvec)]
theorem notCreated_smartSeq {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (p1 p2 : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P (smartSeqHOL p1 p2) =
      (notCreatedSubprogsHOL P p1 && notCreatedSubprogsHOL P p2) := by
  cases p1 <;> simp [smartSeqHOL, notCreatedSubprogsHOL]

/-- HOL `not_created_subprogs_Seq_assoc` (`wordConvsProofScript.sml:523-533`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_Seq_assoc"
  (words_as_type_indexed_bitvec)]
theorem notCreated_seqAssoc {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)),
      notCreatedSubprogsHOL P (seqAssoc p1 p2) =
        (notCreatedSubprogsHOL P p1 && notCreatedSubprogsHOL P p2)
  | p1, .skip => by simp [seqAssoc, notCreatedSubprogsHOL]
  | p1, .seq q1 q2 => by
      rw [seqAssoc, notCreated_seqAssoc P _ q2, notCreated_seqAssoc P p1 q1]
      simp only [notCreatedSubprogsHOL, Bool.and_assoc]
  | p1, .ite v n r q1 q2 => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip q1,
        notCreated_seqAssoc P .skip q2, Bool.true_and]
  | p1, .mustTerminate q => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip q, Bool.true_and]
  | p1, .call none dest args none => by
      rw [seqAssoc, notCreated_smartSeq]
  | p1, .call (some (x1, x2, q1, x3, x4)) dest args none => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip q1, Bool.true_and]
  | p1, .call none dest args (some (y1, q2, y2, y3)) => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip q2, Bool.true_and]
  | p1, .call (some (x1, x2, q1, x3, x4)) dest args (some (y1, q2, y2, y3)) => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip q1,
        notCreated_seqAssoc P .skip q2, Bool.true_and]
  | p1, .loop names body exitNames => by
      rw [seqAssoc, notCreated_smartSeq]
      simp only [notCreatedSubprogsHOL, notCreated_seqAssoc P .skip body, Bool.true_and]
  | p1, .move _ _ | p1, .inst _ | p1, .assign _ _ | p1, .get _ _ | p1, .set _ _
  | p1, .store _ _ | p1, .alloc _ _ | p1, .storeConsts _ _ _ _ _ | p1, .raise _
  | p1, .return _ _ | p1, .break _ | p1, .continue _ | p1, .tick | p1, .opCurrHeap _ _ _
  | p1, .locValue _ _ | p1, .install _ _ _ _ _ | p1, .codeBufferWrite _ _
  | p1, .dataBufferWrite _ _ | p1, .ffi _ _ _ _ _ _ | p1, .shareInst _ _ _ =>
      notCreated_smartSeq P p1 _

theorem notCreated_dropConsts (P : WordLangProgHOL (BitVec width) → Bool)
    (cs : Spt (BitVec width)) : ∀ ls : List Nat, notCreatedSubprogsHOL P (dropConsts cs ls) = true
  | [] => by simp [dropConsts, notCreatedSubprogsHOL]
  | n :: ns => by
      simp only [dropConsts]
      split
      · exact notCreated_dropConsts P cs ns
      · rw [notCreated_smartSeq, notCreated_dropConsts P cs ns]; simp [notCreatedSubprogsHOL]

/-- HOL `not_created_subprogs_drop_consts` (`wordConvsProofScript.sml:535-544`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_drop_consts"
  (words_as_type_indexed_bitvec)]
theorem notCreated_smartSeq_dropConsts {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (cs : Spt (BitVec width)) (ls : List Nat) (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P (smartSeqHOL (dropConsts cs ls) p) = notCreatedSubprogsHOL P p := by
  rw [notCreated_smartSeq, notCreated_dropConsts, Bool.true_and]

/-- `const_fp_loop` keeps `not_created_subprogs` (Flapjack restatement of the HOL
    lemma below on the program component). -/
theorem notCreated_constFpLoop_fst (P : WordLangProgHOL (BitVec width) → Bool)
    (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
    (h : notCreatedSubprogsHOL P p = true) : notCreatedSubprogsHOL P (constFpLoop p cs).1 = true := by
  revert h
  fun_induction constFpLoop p cs <;> intro h <;>
    simp_all [notCreatedSubprogsHOL, notCreated_smartSeq_dropConsts]

/-- HOL `not_created_subprogs_const_fp_loop` (`wordConvsProofScript.sml:546-561`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_const_fp_loop"
  (words_as_type_indexed_bitvec)]
theorem notCreated_constFpLoop {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)) (p1 : WordLangProgHOL (BitVec width))
      (cs1 : Spt (BitVec width)),
      constFpLoop p cs = (p1, cs1) → notCreatedSubprogsHOL P p = true →
      notCreatedSubprogsHOL P p1 = true := by
  intro p cs p1 cs1 he h
  have := notCreated_constFpLoop_fst P p cs h
  rw [he] at this
  exact this

/-- HOL `not_created_subprogs_const_fp` (`wordConvsProofScript.sml:563-570`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_const_fp"
  (words_as_type_indexed_bitvec)]
theorem notCreated_constFp {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P p = true → notCreatedSubprogsHOL P (constFp p) = true :=
  notCreated_constFpLoop_fst P p .ln

theorem destIf_some {p : WordLangProgHOL (BitVec width)} {cmp : Cmp} {lhs : Nat}
    {rhs : WordRegImm (BitVec width)} {b1 b2 : WordLangProgHOL (BitVec width)}
    (h : destIf p = some (cmp, lhs, rhs, b1, b2)) : p = .ite cmp lhs rhs b1 b2 := by
  cases p <;> simp_all [destIf]

/-- HOL `not_created_subprogs_hoist2` (`wordConvsProofScript.sml:572-590`); HOL's free `p3`
    is the leading binder after `P`. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_hoist2"
  (words_as_type_indexed_bitvec)]
theorem notCreated_hoist2 {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (p3 : WordLangProgHOL (BitVec width)) :
    ∀ (N : Nat) (p1 interm dummy p2 : WordLangProgHOL (BitVec width)),
      tryIfHoist2 N p1 interm dummy p2 = some p3 → notCreatedSubprogsHOL P p1 = true →
      notCreatedSubprogsHOL P interm = true → notCreatedSubprogsHOL P p2 = true →
      notCreatedSubprogsHOL P p3 = true := by
  intro N p1 interm dummy p2
  fun_induction tryIfHoist2 N p1 interm dummy p2 <;> intro he h1 hi h2
  all_goals first
    | (simp at he; done)
    | skip
  case case4 =>
    obtain rfl := Option.some.inj he
    apply notCreated_constFp
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨⟨h1.1, hi⟩, h2⟩, ⟨h1.2, hi⟩, h2⟩
  case case7 =>
    obtain rfl := Option.some.inj he
    rename_i n interm dummy p2 p3' p4 cmp lhs rhs br1 br2 hd res1 hr1 res2 hr2
    rw [destIf_some hd] at h1
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, notCreated_constFp P _ ?_⟩
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true]
    exact ⟨⟨⟨h1.2.1, hi⟩, h2⟩, ⟨h1.2.2, hi⟩, h2⟩
  case case8 =>
    rename_i ih
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h1
    exact ih he h1.1 (by simp only [notCreatedSubprogsHOL, Bool.and_eq_true]; exact ⟨h1.2, hi⟩) h2

/-- HOL `not_created_subprogs_simp_duplicate_if` (`wordConvsProofScript.sml:592-605`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_simp_duplicate_if"
  (words_as_type_indexed_bitvec)]
theorem notCreated_simpDuplicateIf {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ p : WordLangProgHOL (BitVec width), notCreatedSubprogsHOL P p = true →
      notCreatedSubprogsHOL P (simpDuplicateIf p) = true := by
  intro p
  fun_induction simpDuplicateIf p <;> intro h
  case case2 ret dest args handler ih2 ih1 =>
    rcases ret with _ | ⟨x1, x2, q1, x3, x4⟩ <;> rcases handler with _ | ⟨y1, q2, y2, y3⟩ <;>
      simp_all [notCreatedSubprogsHOL]
  case case4 p1 p2 _ ih2 ih1 =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h ⊢
    exact ⟨ih2 h.1, ih1 h.2⟩
  case case5 p1 p2 p3 hh ih2 ih1 =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h
    rw [notCreated_seqAssoc, Bool.and_eq_true]
    refine ⟨rfl, ?_⟩
    simp only [tryIfHoist1] at hh
    split at hh
    · simp at hh
    · exact notCreated_hoist2 P p3 _ _ _ _ _ hh (ih2 h.1) rfl (ih1 h.2)
  case case7 => exact h
  all_goals simp_all [notCreatedSubprogsHOL]

/-- `push_out_if_aux` keeps `not_created_subprogs` of the program component
    (Flapjack infrastructure for the HOL lemma below). -/
theorem notCreated_pushOutIfAux (P : WordLangProgHOL (BitVec width) → Bool)
    (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P (pushOutIfAux p).1 = notCreatedSubprogsHOL P p := by
  fun_induction pushOutIfAux p <;>
    simp_all [notCreatedSubprogsHOL, Bool.and_comm]

/-- HOL `not_created_subprogs_push_out_if` (`wordConvsProofScript.sml:607-620`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "not_created_subprogs_push_out_if"
  (words_as_type_indexed_bitvec)]
theorem notCreated_pushOutIf {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ p : WordLangProgHOL (BitVec width),
      notCreatedSubprogsHOL P (pushOutIf p) = notCreatedSubprogsHOL P p :=
  notCreated_pushOutIfAux P

/-- HOL `compile_exp_not_created_subprogs` (`wordConvsProofScript.sml:622-629`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_exp_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_compileExp {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P p = true → notCreatedSubprogsHOL P (compileExp p) = true := by
  intro h
  simp only [compileExp]
  rw [notCreated_pushOutIf]
  apply notCreated_simpDuplicateIf
  apply notCreated_constFp
  rw [notCreated_seqAssoc, h]
  rfl

end WordSimp

section InstSelect

open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width]

/-- HOL `inst_select_exp_not_created_subprogs` (`wordConvsProofScript.sml:884-892`); HOL's free
    `P c c' n exp` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_exp_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_instSelectExp {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (c : AsmConfigExact width) (tar temp : Nat) (exp : WordLangExpHOL (BitVec width)) :
    notCreatedSubprogsHOL P (instSelectExp c tar temp exp) = true := by
  induction exp using (measure (fun e : WordLangExpHOL (BitVec width) => sizeOf e)).wf.induction
      generalizing tar temp with
  | h exp ih =>
    fun_cases instSelectExp c tar temp exp <;>
      simp_all +zetaDelta [instSelectExp, notCreatedSubprogsHOL]
    all_goals
      repeat' first
        | (apply ih; simp_wf; omega)
        | simp_all +zetaDelta [notCreatedSubprogsHOL, isLookupCurrHeap]
        | split
        | constructor
    case case3 =>
      rename_i child notAddress
      apply ih child
      change sizeOf child < sizeOf (WordLangExpHOL.load child)
      simp

/-- HOL `inst_select_not_created_subprogs` (`wordConvsProofScript.sml:894-907`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "inst_select_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_instSelect {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (c : AsmConfigExact width) (n : Nat) (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (instSelect c n prog) = true := by
  induction prog using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h prog ih =>
    intro hp
    fun_cases instSelect c n prog <;>
      simp_all +zetaDelta [notCreatedSubprogsHOL, notCreated_instSelectExp]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | simp_all +zetaDelta [notCreatedSubprogsHOL]
        | split
        | constructor

end InstSelect

end Flapjack.WordConvs
