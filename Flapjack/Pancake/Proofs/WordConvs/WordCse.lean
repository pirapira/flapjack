import Flapjack.Compiler.Backend.WordCse.Proofs.Conventions
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Pancake.WordConvs.CodeLabels
import Flapjack.Pancake.WordConvs.WfCutsets

/-!
# `wordConvsProof` `word_common_subexp_elim` group

The label, handler, sub-program and convention preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml:1605-1850`. Each is a
consequence of the `word_cse` output shape `CseOut`: structure is preserved and
only leaf statements are replaced by moves.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Encoders.Asm

section Shape

variable {width : Nat} [NeZero width]

omit [NeZero width] in
theorem extractLabels_cseOut {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q) :
    extractLabels q = extractLabels p := by
  induction h with
  | refl => rfl
  | move p _ _ hl => cases p <;> simp_all [CseLeaf, extractLabels]
  | seq _ _ _ _ _ _ iha ihb => simp [extractLabels, iha, ihb]
  | ite _ _ _ _ _ _ _ _ _ iha ihb => simp [extractLabels, iha, ihb]
  | mustTerminate _ _ _ ih => simp [extractLabels, ih]
  | loop _ _ _ _ _ ih => simp [extractLabels, ih]

theorem notCreatedSubprogs_cseOut (P : WordLangProgHOL (BitVec width) → Bool)
    {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q)
    (hp : notCreatedSubprogsHOL P p = true) : notCreatedSubprogsHOL P q = true := by
  induction h with
  | refl => exact hp
  | move => simp [notCreatedSubprogsHOL]
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨hp.1, ih hp.2⟩
  | loop _ _ _ _ _ ih => simp only [notCreatedSubprogsHOL] at hp ⊢; exact ih hp

theorem goodHandlers_cseOut (n : Nat) {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q) :
    goodHandlersHOL n q = goodHandlersHOL n p := by
  induction h with
  | refl => rfl
  | move p _ _ hl => cases p <;> simp_all [CseLeaf, goodHandlersHOL]
  | seq _ _ _ _ _ _ iha ihb => simp [goodHandlersHOL, iha, ihb]
  | ite _ _ _ _ _ _ _ _ _ iha ihb => simp [goodHandlersHOL, iha, ihb]
  | mustTerminate _ _ _ ih => simp [goodHandlersHOL, ih]
  | loop _ _ _ _ _ ih => simp [goodHandlersHOL, ih]

theorem getCodeLabels_cseOut {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q) :
    getCodeLabelsHOL q ⊆ getCodeLabelsHOL p := by
  induction h with
  | refl => exact subset_rfl
  | move => simp [getCodeLabelsHOL]
  | seq _ _ _ _ _ _ iha ihb => simp only [getCodeLabelsHOL]; exact Set.union_subset_union iha ihb
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [getCodeLabelsHOL]; exact Set.union_subset_union iha ihb
  | mustTerminate _ _ _ ih => simpa [getCodeLabelsHOL] using ih
  | loop _ _ _ _ _ ih => simpa [getCodeLabelsHOL] using ih

omit [NeZero width] in
theorem flatExpConventions_cseOut {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q)
    (hp : flatExpConventions p = true) : flatExpConventions q = true := by
  induction h with
  | refl => exact hp
  | move => simp [flatExpConventions]
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [flatExpConventions, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [flatExpConventions, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [flatExpConventions] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [flatExpConventions] at hp ⊢; exact ih hp

theorem wfCutsets_cseOut {p q : WordLangProgHOL (BitVec width)} (h : CseOut p q)
    (hp : wfCutsets p) : wfCutsets q := by
  induction h with
  | refl => exact hp
  | move => simp [wfCutsets]
  | seq _ _ _ _ _ _ iha ihb => simp only [wfCutsets] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ iha ihb => simp only [wfCutsets] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [wfCutsets] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [wfCutsets] at hp ⊢; exact ⟨hp.1, hp.2.1, ih hp.2.2⟩

theorem wordCommonSubexpElim_out (p : WordLangProgHOL (BitVec width)) :
    CseOut p (wordCommonSubexpElim p) := by
  unfold wordCommonSubexpElim
  have := wordCse_out p emptyData
  rcases h : wordCse emptyData p with ⟨d, q⟩
  rw [h] at this
  exact this

end Shape

/-- HOL `word_cse_extract_labels` (`wordConvsProofScript.sml:1606-1626`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_extract_labels"
  (words_as_type_indexed_bitvec)]
theorem word_cse_extract_labels {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (d d1 : Knowledge) (p1 : WordLangProgHOL (BitVec width)),
      wordCse d p = (d1, p1) → extractLabels p1 = extractLabels p := by
  intro p d d1 p1 h
  have := wordCse_out p d
  rw [h] at this
  exact extractLabels_cseOut this

/-- HOL `extract_labels_word_common_subexp_elim` (`wordConvsProofScript.sml:1628-1633`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "extract_labels_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem extract_labels_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    extractLabels (wordCommonSubexpElim p) = extractLabels p :=
  extractLabels_cseOut (wordCommonSubexpElim_out p)

/-- HOL `word_cseInst_not_created_subprogs` (`wordConvsProofScript.sml:1635-1648`);
HOL's free predicate `P` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_cseInst_not_created_subprogs" (words_as_type_indexed_bitvec)]
theorem word_cseInst_not_created_subprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (env : Knowledge) (i : HolInst width), notCreatedSubprogsHOL P (wordCseInst env i).2 = true := by
  intro env i
  exact notCreatedSubprogs_cseOut P (wordCseInst_out env i) (by simp [notCreatedSubprogsHOL])

/-- HOL `word_cse_not_created_subprogs` (`wordConvsProofScript.sml:1650-1662`);
HOL's free predicate `P` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem word_cse_not_created_subprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (env : Knowledge),
      notCreatedSubprogsHOL P p = true → notCreatedSubprogsHOL P (wordCse env p).2 = true :=
  fun p env => notCreatedSubprogs_cseOut P (wordCse_out p env)

/-- HOL `word_common_subexp_elim_not_created_subprogs` (`wordConvsProofScript.sml:1664-1670`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_common_subexp_elim_not_created_subprogs" (words_as_type_indexed_bitvec)]
theorem word_common_subexp_elim_not_created_subprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true →
    notCreatedSubprogsHOL P (wordCommonSubexpElim prog) = true :=
  notCreatedSubprogs_cseOut P (wordCommonSubexpElim_out prog)

/-- HOL `word_good_handlers_word_common_subexp_elim` (`wordConvsProofScript.sml:1672-1693`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem word_good_handlers_word_common_subexp_elim {width : Nat} [NeZero width] (q : Nat)
    (p : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL q (wordCommonSubexpElim p) = true ↔ goodHandlersHOL q p = true := by
  rw [goodHandlers_cseOut q (wordCommonSubexpElim_out p)]

/-- HOL `word_cse_get_code_labels` (`wordConvsProofScript.sml:1698-1738`): CSE may
only drop code labels (a repeated `LocValue` becomes a `Move`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_get_code_labels"
  (words_as_type_indexed_bitvec)]
theorem word_cse_get_code_labels {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (data data' : Knowledge) (q : WordLangProgHOL (BitVec width)),
      wordCse data p = (data', q) → getCodeLabelsHOL q ⊆ getCodeLabelsHOL p := by
  intro p data data' q h
  have := wordCse_out p data
  rw [h] at this
  exact getCodeLabels_cseOut this

/-- HOL `word_get_code_labels_word_common_subexp_elim` (`wordConvsProofScript.sml:1740-1747`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem word_get_code_labels_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (wordCommonSubexpElim p) ⊆ getCodeLabelsHOL p :=
  getCodeLabels_cseOut (wordCommonSubexpElim_out p)

/-- HOL `word_cse_flat_exp_conventions` (`wordConvsProofScript.sml:1749-1790`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_flat_exp_conventions"
  (words_as_type_indexed_bitvec)]
theorem word_cse_flat_exp_conventions {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (data data' : Knowledge) (q : WordLangProgHOL (BitVec width)),
      flatExpConventions p = true ∧ wordCse data p = (data', q) → flatExpConventions q = true := by
  rintro p data data' q ⟨hp, h⟩
  have := wordCse_out p data
  rw [h] at this
  exact flatExpConventions_cseOut this hp

/-- HOL `flat_exp_conventions_word_common_subexp_elim` (`wordConvsProofScript.sml:1792-1799`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem flat_exp_conventions_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    flatExpConventions p = true → flatExpConventions (wordCommonSubexpElim p) = true :=
  flatExpConventions_cseOut (wordCommonSubexpElim_out p)

/-- HOL `word_cse_wf_cutsets` (`wordConvsProofScript.sml:1801-1841`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_cse_wf_cutsets"
  (words_as_type_indexed_bitvec)]
theorem word_cse_wf_cutsets {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (data data' : Knowledge) (q : WordLangProgHOL (BitVec width)),
      wfCutsets p ∧ wordCse data p = (data', q) → wfCutsets q := by
  rintro p data data' q ⟨hp, h⟩
  have := wordCse_out p data
  rw [h] at this
  exact wfCutsets_cseOut this hp

/-- HOL `wf_cutsets_word_common_subexp_elim` (`wordConvsProofScript.sml:1843-1849`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "wf_cutsets_word_common_subexp_elim" (words_as_type_indexed_bitvec)]
theorem wf_cutsets_word_common_subexp_elim {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    wfCutsets p → wfCutsets (wordCommonSubexpElim p) :=
  wfCutsets_cseOut (wordCommonSubexpElim_out p)

end Flapjack.WordConvs
