import Flapjack.Compiler.Backend.WordCse.Transform
import Flapjack.Pancake.WordConvs.FullInstOkLess

/-!
# `word_cseProof`: syntactic conventions

Counterpart of the `SYNTACTIC CONVENTIONS` section of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (3806-4038): `word_cse`
emits only original instructions or moves, so `full_inst_ok_less`,
`pre_alloc_conventions` and `every_inst` of `distinct_tar_reg`/`two_reg_inst`
transport to its output with no well-formedness premise. HOL's
`every_inst P` over `'a inst` is `everyInst (fun i => P (HolInst.ofWordLangInst i))`
over the reviewed instruction mirror, as in the accepted `inst_select`
convention theorems.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

section Shape

variable {width : Nat} [NeZero width]

/-- The leaf statements `word_cse` may replace by a move (Flapjack
    infrastructure). -/
def CseLeaf : WordLangProgHOL (BitVec width) → Prop
  | .inst _ | .get _ _ | .set _ _ | .opCurrHeap _ _ _ | .locValue _ _ => True
  | _ => False

/-- The output shape of `word_cse`: each instruction-level program is kept or
    replaced by a move, and structure is preserved (Flapjack infrastructure for
    the HOL convention proofs). -/
inductive CseOut : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) → Prop
  | refl (p) : CseOut p p
  | move (p) (pri : Nat) (rs : List (Nat × Nat)) : CseLeaf p → CseOut p (.move pri rs)
  | seq (a b a' b') : CseOut a a' → CseOut b b' → CseOut (.seq a b) (.seq a' b')
  | ite (cmp r ri a b a' b') : CseOut a a' → CseOut b b' →
      CseOut (.ite cmp r ri a b) (.ite cmp r ri a' b')
  | mustTerminate (a a') : CseOut a a' → CseOut (.mustTerminate a) (.mustTerminate a')
  | loop (n a e a') : CseOut a a' → CseOut (.loop n a e) (.loop n a' e)

theorem addToDataAux_out (data : Knowledge) (r : Nat) (i : List Nat) (p : WordLangProgHOL (BitVec width)) :
    (addToDataAux data r i p).2 = p ∨ ∃ pri rs, (addToDataAux data r i p).2 = .move pri rs := by
  unfold addToDataAux
  split <;> (try split) <;> simp

theorem addToLoadAux_out (data : Knowledge) (r : Nat) (i : List Nat) (p : WordLangProgHOL (BitVec width)) :
    (addToLoadAux data r i p).2 = p ∨ ∃ pri rs, (addToLoadAux data r i p).2 = .move pri rs := by
  unfold addToLoadAux
  split <;> (try split) <;> simp

omit [NeZero width] in
theorem cseOut_of_or (p q : WordLangProgHOL (BitVec width)) (hl : CseLeaf p)
    (h : q = p ∨ ∃ pri rs, q = .move pri rs) : CseOut p q := by
  rcases h with rfl | ⟨pri, rs, rfl⟩
  · exact .refl _
  · exact .move _ pri rs hl

theorem wordCseInst_out (data : Knowledge) (j : HolInst width) :
    CseOut (.inst j.toWordLangInst) (wordCseInst data j).2 := by
  apply cseOut_of_or _ _ (by trivial)
  cases j with
  | skip => simp [wordCseInst]
  | const r w =>
    simp only [wordCseInst]
    split
    · simp
    · unfold addToDataConst; dsimp only; split <;> simp [HolInst.toWordLangInst]
  | arith a =>
    simp only [wordCseInst]
    split
    · exact addToDataAux_out _ _ _ _
    · simp
  | mem op r ad =>
    cases ad with
    | addr a ofs =>
      simp only [wordCseInst]
      split
      · simp
      · split
        · simp
        · exact addToLoadAux_out _ _ _ _
  | fp f => simp [wordCseInst]

theorem wordCse_out : ∀ (p : WordLangProgHOL (BitVec width)) (data : Knowledge),
    CseOut p (wordCse data p).2
  | .move r rs, _ => by simp only [wordCse]; exact .refl _
  | .inst i, data => by
      simp only [wordCse]
      have := wordCseInst_out data (HolInst.ofWordLangInst i)
      rwa [HolInst.to_of] at this
  | .get r x, data => by
      simp only [wordCse, getClause]
      apply cseOut_of_or _ _ (by trivial)
      split <;> split <;> simp
  | .set x e, data => by
      simp only [wordCse, setClause]
      apply cseOut_of_or _ _ (by trivial)
      split
      · simp
      · split
        · simp
        · split <;> simp
  | .mustTerminate p, data => by simp only [wordCse]; exact .mustTerminate _ _ (wordCse_out p data)
  | .call _ _ _ _, _ => by simp only [wordCse]; exact .refl _
  | .seq p1 p2, data => by
      simp only [wordCse]
      exact .seq _ _ _ _ (wordCse_out p1 data) (wordCse_out p2 _)
  | .ite _ _ _ p1 p2, data => by
      simp only [wordCse]
      exact .ite _ _ _ _ _ _ _ (wordCse_out p1 data) (wordCse_out p2 data)
  | .opCurrHeap b r1 r2, data => by
      simp only [wordCse]
      apply cseOut_of_or _ _ (by trivial)
      split
      · simp
      · exact addToDataAux_out _ _ _ _
  | .locValue r l, data => by
      simp only [wordCse]
      exact cseOut_of_or _ _ (by trivial) (addToDataAux_out _ _ _ _)
  | .skip, _ => .refl _
  | .store _ _, _ => .refl _
  | .assign _ _, _ => .refl _
  | .raise _, _ => .refl _
  | .return _ _, _ => .refl _
  | .tick, _ => .refl _
  | .alloc _ _, _ => .refl _
  | .install _ _ _ _ _, _ => .refl _
  | .codeBufferWrite _ _, _ => .refl _
  | .dataBufferWrite _ _, _ => .refl _
  | .ffi _ _ _ _ _ _, _ => .refl _
  | .storeConsts _ _ _ _ _, _ => by simp only [wordCse]; exact .refl _
  | .shareInst _ _ _, _ => by simp only [wordCse]; exact .refl _
  | .loop _ c _, _ => by simp only [wordCse]; exact .loop _ _ _ _ (wordCse_out c emptyData)
  | .break _, _ => .refl _
  | .continue _, _ => .refl _

omit [NeZero width] in
theorem everyInst_cseOut (P : WordLangInst (BitVec width) → Bool) {p q : WordLangProgHOL (BitVec width)}
    (h : CseOut p q) (hp : everyInst P p = true) : everyInst P q = true := by
  induction h with
  | refl => exact hp
  | move => rfl
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [everyInst, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [everyInst, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [everyInst] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [everyInst] at hp ⊢; exact ih hp

omit [NeZero width] in
theorem fullInstOkLessWith_cseOut (io : WordLangInst (BitVec width) → Bool)
    (ao : HolMemop → BitVec width → Bool) {p q : WordLangProgHOL (BitVec width)}
    (h : CseOut p q) (hp : fullInstOkLessWith io ao p = true) : fullInstOkLessWith io ao q = true := by
  induction h with
  | refl => exact hp
  | move => rfl
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [fullInstOkLessWith, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [fullInstOkLessWith, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [fullInstOkLessWith] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [fullInstOkLessWith] at hp ⊢; exact ih hp

theorem preAllocConventionsHOL_cseOut {p q : WordLangProgHOL (BitVec width)}
    (h : CseOut p q) (hp : preAllocConventionsHOL p = true) : preAllocConventionsHOL q = true := by
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at hp ⊢
  induction h with
  | refl => exact hp
  | move => exact ⟨rfl, rfl⟩
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at hp ⊢
    exact ⟨⟨(iha ⟨hp.1.1, hp.2.1⟩).1, (ihb ⟨hp.1.2, hp.2.2⟩).1⟩,
      (iha ⟨hp.1.1, hp.2.1⟩).2, (ihb ⟨hp.1.2, hp.2.2⟩).2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at hp ⊢
    exact ⟨⟨(iha ⟨hp.1.1, hp.2.1⟩).1, (ihb ⟨hp.1.2, hp.2.2⟩).1⟩,
      (iha ⟨hp.1.1, hp.2.1⟩).2, (ihb ⟨hp.1.2, hp.2.2⟩).2⟩
  | mustTerminate _ _ _ ih =>
    simp only [everyStackVarHOL, callArgConventionHOL] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih =>
    simp only [everyStackVarHOL, callArgConventionHOL] at hp ⊢; exact ih hp

end Shape

/-- Exact HOL `word_cse_full_inst_ok_less` (`word_cseProof:3813-3836`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_full_inst_ok_less"
  (words_as_type_indexed_bitvec)]
theorem word_cse_full_inst_ok_less {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (data : Knowledge) (c : AsmConfigExact width) (data' : Knowledge) (q : WordLangProgHOL (BitVec width))
    (h : fullInstOkLessExact c p = true ∧ wordCse data p = (data', q)) : fullInstOkLessExact c q = true := by
  obtain ⟨hp, hw⟩ := h
  have := wordCse_out p data
  rw [hw] at this
  exact fullInstOkLessWith_cseOut _ _ this hp

/-- Exact HOL `word_cse_pre_alloc_conventions`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_pre_alloc_conventions"
  (words_as_type_indexed_bitvec)]
theorem word_cse_pre_alloc_conventions {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (data data' : Knowledge) (q : WordLangProgHOL (BitVec width))
    (h : preAllocConventionsHOL p = true ∧ wordCse data p = (data', q)) : preAllocConventionsHOL q = true := by
  obtain ⟨hp, hw⟩ := h
  have := wordCse_out p data
  rw [hw] at this
  exact preAllocConventionsHOL_cseOut this hp

/-- Exact HOL `word_cse_every_inst_distinct_tar_reg`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_every_inst_distinct_tar_reg"
  (words_as_type_indexed_bitvec)]
theorem word_cse_every_inst_distinct_tar_reg {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) (data data' : Knowledge) (q : WordLangProgHOL (BitVec width))
    (h : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true ∧
      wordCse data p = (data', q)) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) q = true := by
  obtain ⟨hp, hw⟩ := h
  have := wordCse_out p data
  rw [hw] at this
  exact everyInst_cseOut _ this hp

/-- Exact HOL `word_cse_every_inst_two_reg`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_every_inst_two_reg"
  (words_as_type_indexed_bitvec)]
theorem word_cse_every_inst_two_reg {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) (data data' : Knowledge) (q : WordLangProgHOL (BitVec width))
    (h : everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) p = true ∧
      wordCse data p = (data', q)) :
    everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) q = true := by
  obtain ⟨hp, hw⟩ := h
  have := wordCse_out p data
  rw [hw] at this
  exact everyInst_cseOut _ this hp

/-- Exact HOL `every_inst_distinct_tar_reg_word_common_subexp_elim`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml"
  "every_inst_distinct_tar_reg_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem every_inst_distinct_tar_reg_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width))
    (h : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) (wordCommonSubexpElim p) = true :=
  everyInst_cseOut _ (wordCse_out p emptyData) h

/-- Exact HOL `pre_alloc_conventions_word_common_subexp_elim`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml"
  "pre_alloc_conventions_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem pre_alloc_conventions_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) (h : preAllocConventionsHOL p = true) :
    preAllocConventionsHOL (wordCommonSubexpElim p) = true :=
  preAllocConventionsHOL_cseOut (wordCse_out p emptyData) h

/-- Exact HOL `full_inst_ok_less_word_common_subexp_elim`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml"
  "full_inst_ok_less_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem full_inst_ok_less_word_common_subexp_elim {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (h : fullInstOkLessExact ac p = true) : fullInstOkLessExact ac (wordCommonSubexpElim p) = true :=
  fullInstOkLessWith_cseOut _ _ (wordCse_out p emptyData) h

end Flapjack.Compiler.Backend.WordCse
