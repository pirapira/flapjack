import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileWordToWord
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoMtCode
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedTail
import Flapjack.Pancake.Proofs.WordConvs.RemoveMustTerminate

/-!
# `word_to_wordProof`: syntactic preservation group

The `no_share_inst` group (`word_to_wordProofScript.sml:906-956`),
`code_rel_not_created_subprogs` and its `no_alloc`/`no_install` instances
(1067-1090), and the `no_mt`/`code_rel_ext` group with `code_rel_no_share_inst`
(2102-2217): syntactic facts about `inst_select`, `remove_must_terminate`,
`full_compile_single`, `compile` and `code_rel` used by the Pancake semantics
theorems of the script.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordInst
  Flapjack.Compiler.Backend.WordRemove Flapjack.WordConvs

/-- HOL `cond16bit_inst_select_exp'` (`word_to_wordProofScript.sml:906-915`); HOL's free
    `x c t1 t2 exp` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "cond16bit_inst_select_exp'"
  (words_as_type_indexed_bitvec)]
theorem cond16bit_inst_select_exp' {width : Nat} [NeZero width] (x : WordLangProgHOL (BitVec width))
    (c : AsmConfigExact width) (t1 t2 : Nat) (exp : WordLangExpHOL (BitVec width)) :
    x = instSelectExp c t1 t2 exp → noShareInstSubprogsHOL x = true ∨ c.isa ≠ .ag32 := by
  rintro rfl
  left
  rw [noShareInstSubprogsHOL_eq_notCreated]
  exact notCreated_instSelectExp _ c t1 t2 exp

/-- HOL `cond16bit_inst_select` (`word_to_wordProofScript.sml:919-929`); HOL's free
    `x c n p` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "cond16bit_inst_select"
  (words_as_type_indexed_bitvec)]
theorem cond16bit_inst_select {width : Nat} [NeZero width] (x : WordLangProgHOL (BitVec width))
    (c : AsmConfigExact width) (n : Nat) (p : WordLangProgHOL (BitVec width)) :
    x = instSelect c n p ∧ (noShareInstSubprogsHOL p = true ∨ c.isa ≠ .ag32) →
      noShareInstSubprogsHOL x = true ∨ c.isa ≠ .ag32 := by
  rintro ⟨rfl, hp | hp⟩
  · left
    rw [noShareInstSubprogsHOL_eq_notCreated] at hp ⊢
    exact notCreated_instSelect _ c n p hp
  · exact .inr hp

/-- `remove_must_terminate` preserves `not_created_subprogs` for every predicate
    (Flapjack infrastructure for HOL's `remove_must_terminate_ind` proofs below:
    the checker only inspects normalized nodes, which the pass keeps). -/
theorem notCreated_removeMustTerminate {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P p = true → notCreatedSubprogsHOL P (removeMustTerminate p) = true := by
  refine removeMustTerminate_induct (fun p p' => notCreatedSubprogsHOL P p = true →
    notCreatedSubprogsHOL P p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
  all_goals intros
  all_goals simp_all [notCreatedSubprogsHOL]

/-- HOL `remove_must_terminate_no_share_inst` (`word_to_wordProofScript.sml:931-938`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "remove_must_terminate_no_share_inst" (words_as_type_indexed_bitvec)]
theorem remove_must_terminate_no_share_inst {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    noShareInstSubprogsHOL p = true → noShareInstSubprogsHOL (removeMustTerminate p) = true := by
  rw [noShareInstSubprogsHOL_eq_notCreated, noShareInstSubprogsHOL_eq_notCreated]
  exact notCreated_removeMustTerminate _ p

/-- HOL `full_compile_single_no_share_inst` (`word_to_wordProofScript.sml:940-954`); HOL's
    free `prog_info two_reg_arith reg_count alg c` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "full_compile_single_no_share_inst" (words_as_type_indexed_bitvec)]
theorem full_compile_single_no_share_inst {width : Nat} [NeZero width]
    (progInfo : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat))
    (twoRegArith : Bool) (regCount alg : Nat) (c : AsmConfigExact width) :
    noShareInstSubprogsHOL progInfo.1.2.2 = true →
      noShareInstSubprogsHOL (fullCompileSingle twoRegArith regCount alg c progInfo).2.2 = true := by
  intro h
  rw [fullCompileSingle_eq]
  apply remove_must_terminate_no_share_inst
  rw [noShareInstSubprogsHOL_eq_notCreated] at h ⊢
  exact compile_single_not_created_subprogs _ twoRegArith regCount alg c progInfo h

/-- HOL `code_rel_not_created_subprogs` (`word_to_wordProofScript.sml:1067-1080`); HOL's
    free `P op args c1 sz v c2 v'` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "code_rel_not_created_subprogs" (words_as_type_indexed_bitvec)]
theorem code_rel_not_created_subprogs {width : Nat} [NeZero width] {locWidth : Nat} [NeZero locWidth]
    {γ : Type}
    (P : WordLangProgHOL (BitVec width) → Bool) (op : Option Nat) (args : List (WordLocW locWidth))
    (c1 : Spt (Nat × WordLangProgHOL (BitVec width))) (sz : Spt γ)
    (v : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ)
    (c2 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (v' : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ) :
    wordSemFindCode op args c1 sz = some v ∧ codeRel c1 c2 ∧
      notCreatedSubprogsHOL P v.2.1 = true ∧ wordSemFindCode op args c2 sz = some v' →
    notCreatedSubprogsHOL P v'.2.1 = true := by
  rintro ⟨h1, hrel, hP, h2⟩
  have entry : ∀ loc ar e, sptLookup loc c1 = some (ar, e) → notCreatedSubprogsHOL P e = true →
      ∀ ar' e', sptLookup loc c2 = some (ar', e') → notCreatedSubprogsHOL P e' = true := by
    intro loc ar e hl he ar' e' hl'
    obtain ⟨col, t, k, a, c, hl2⟩ := hrel loc _ hl
    rw [hl'] at hl2
    cases hl2
    exact compile_single_not_created_subprogs P t k a c ((loc, ar, e), col) he
  cases op with
  | some p =>
    simp only [wordSemFindCode] at h1 h2
    split at h1 <;> try cases h1
    rename_i ar e hl
    split at h1 <;> cases h1
    split at h2 <;> try cases h2
    rename_i ar' e' hl'
    split at h2 <;> cases h2
    exact entry p ar e hl hP ar' e' hl'
  | none =>
    simp only [wordSemFindCode] at h1 h2
    split at h1 <;> try cases h1
    split at h2 <;> try cases h2
    split at h1 <;> try cases h1
    rename_i loc _
    split at h1 <;> try cases h1
    rename_i ar e hl
    split at h1 <;> cases h1
    split at h2 <;> try cases h2
    rename_i loc' _
    split at h2 <;> try cases h2
    rename_i ar' e' hl'
    split at h2 <;> cases h2
    have : loc' = loc := by simp_all
    subst this
    exact entry loc' ar e hl hP ar' e' hl'

/-- HOL `code_rel_no_alloc` (`word_to_wordProofScript.sml:1084-1085`, `[local]`): the
    `no_alloc` instance of `code_rel_not_created_subprogs`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_alloc"
  (words_as_type_indexed_bitvec)]
theorem code_rel_no_alloc {width : Nat} [NeZero width] {locWidth : Nat} [NeZero locWidth] {γ : Type}
    (op : Option Nat)
    (args : List (WordLocW locWidth)) (c1 : Spt (Nat × WordLangProgHOL (BitVec width))) (sz : Spt γ)
    (v : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ)
    (c2 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (v' : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ) :
    wordSemFindCode op args c1 sz = some v ∧ codeRel c1 c2 ∧
      noAllocSubprogsHOL v.2.1 = true ∧ wordSemFindCode op args c2 sz = some v' →
    noAllocSubprogsHOL v'.2.1 = true := by
  simp only [noAllocSubprogsHOL_eq_notCreated]
  exact code_rel_not_created_subprogs _ op args c1 sz v c2 v'

/-- HOL `code_rel_no_install` (`word_to_wordProofScript.sml:1087-1088`, `[local]`): the
    `no_install` instance of `code_rel_not_created_subprogs`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_install"
  (words_as_type_indexed_bitvec)]
theorem code_rel_no_install {width : Nat} [NeZero width] {locWidth : Nat} [NeZero locWidth] {γ : Type}
    (op : Option Nat)
    (args : List (WordLocW locWidth)) (c1 : Spt (Nat × WordLangProgHOL (BitVec width))) (sz : Spt γ)
    (v : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ)
    (c2 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (v' : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ) :
    wordSemFindCode op args c1 sz = some v ∧ codeRel c1 c2 ∧
      noInstallSubprogsHOL v.2.1 = true ∧ wordSemFindCode op args c2 sz = some v' →
    noInstallSubprogsHOL v'.2.1 = true := by
  simp only [noInstallSubprogsHOL_eq_notCreated]
  exact code_rel_not_created_subprogs _ op args c1 sz v c2 v'

/-- HOL `no_mt_remove_must_terminate_const` (`word_to_wordProofScript.sml:2102-2109`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "no_mt_remove_must_terminate_const" (words_as_type_indexed_bitvec)]
theorem no_mt_remove_must_terminate_const {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) :
    noMtSubprogsHOL prog = true → removeMustTerminate prog = prog := by
  rw [noMtSubprogsHOL_eq_notCreated]
  refine removeMustTerminate_induct (fun p p' => notCreatedSubprogsHOL
    (fun q => by classical exact decide (q ≠ .mustTerminate .skip)) p = true → p' = p)
    (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ prog
  all_goals intros
  all_goals simp_all [notCreatedSubprogsHOL]

/-- HOL `no_mt_full_compile_single` (`word_to_wordProofScript.sml:2111-2123`); HOL's free
    `x tt kk aa c` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_full_compile_single"
  (words_as_type_indexed_bitvec)]
theorem no_mt_full_compile_single {width : Nat} [NeZero width]
    (x : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat))
    (tt : Bool) (kk aa : Nat) (c : AsmConfigExact width) :
    noMtSubprogsHOL x.1.2.2 = true → fullCompileSingle tt kk aa c x = compileSingle tt kk aa c x := by
  intro h
  rw [fullCompileSingle_eq]
  rw [noMtSubprogsHOL_eq_notCreated] at h
  have h' := compile_single_not_created_subprogs _ tt kk aa c x h
  rw [← noMtSubprogsHOL_eq_notCreated] at h'
  simp only [no_mt_remove_must_terminate_const _ h']

/-- First-match association lookup finds every member of a list whose keys are
    distinct (Flapjack infrastructure for HOL's `ALOOKUP_ALL_DISTINCT_EL`). -/
theorem sptAListLookup_of_mem_nodup {α : Type} :
    ∀ (entries : List (Nat × α)) (key : Nat) (value : α),
      (entries.map Prod.fst).Nodup → (key, value) ∈ entries →
      sptAListLookup key entries = some value
  | [], _, _, _, hmem => by simp at hmem
  | (other, w) :: entries, key, value, hnd, hmem => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [sptAListLookup]
    rcases List.mem_cons.mp hmem with h | h
    · cases h; simp
    · have hne : key ≠ other := by
        rintro rfl
        exact hnd.1 ⟨(key, value), h, rfl⟩
      rw [if_neg hne]
      exact sptAListLookup_of_mem_nodup entries key value hnd.2 h

/-- HOL `no_mt_code_full_compile_single` (`word_to_wordProofScript.sml:2125-2140`); HOL's
    free `progs x tt kk aa co` are explicit and `ALL_DISTINCT` is `List.Nodup`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "no_mt_code_full_compile_single" (words_as_type_indexed_bitvec)]
theorem no_mt_code_full_compile_single {width : Nat} [NeZero width]
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (x : List (Option (Spt Nat)))
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) :
    WordProps.noMtCode (sptFromAList progs) ∧ (progs.map Prod.fst).Nodup ∧ x.length = progs.length →
      (progs.zip x).map (fullCompileSingle tt kk aa co) =
        (progs.zip x).map (compileSingle tt kk aa co) := by
  rintro ⟨hmt, hnd, -⟩
  apply List.map_congr_left
  rintro ⟨⟨n, ar, p⟩, col⟩ hmem
  apply no_mt_full_compile_single
  apply hmt n ar p
  rw [sptLookup_sptFromAList]
  exact sptAListLookup_of_mem_nodup progs n (ar, p) hnd (List.of_mem_zip hmem).1

/-- HOL `code_rel_ext_def` (`word_to_wordProofScript.sml:2144-2151`): every source entry is
    compiled by some `full_compile_single` instance. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_ext_def" 2144
  (words_as_type_indexed_bitvec)]
def codeRelExt {width : Nat} [NeZero width] (code l : Spt (Nat × WordLangProgHOL (BitVec width))) :
    Prop :=
  ∀ (n : Nat) (p1 : Nat) (p2 : WordLangProgHOL (BitVec width)),
    some (p1, p2) = sptLookup n code →
      ∃ (t' : Bool) (k' a' : Nat) (c' : AsmConfigExact width) (col : Option (Spt Nat)),
        some (fullCompileSingle t' k' a' c' ((n, p1, p2), col)).2 = sptLookup n l

/-- First-match lookup through the entry-wise `full_compile_single` of `compile`
    (Flapjack infrastructure for HOL's induction in `code_rel_ext_word_to_word`). -/
theorem sptAListLookup_map_fullCompileSingle {width : Nat} [NeZero width] (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) :
    ∀ (code : List (Nat × Nat × WordLangProgHOL (BitVec width))) (os : List (Option (Spt Nat))),
      os.length = code.length → ∀ n p1 p2, sptAListLookup n code = some (p1, p2) →
      ∃ col, sptAListLookup n ((code.zip os).map (fullCompileSingle t k a c)) =
        some (fullCompileSingle t k a c ((n, p1, p2), col)).2
  | [], _, _, _, _, _, h => by simp [sptAListLookup] at h
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | (m, ar, p) :: code, o :: os, hl, n, p1, p2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.zip_cons_cons, List.map_cons]
    simp only [sptAListLookup] at h
    have hname : (fullCompileSingle t k a c ((m, ar, p), o)).1 = m := rfl
    by_cases hnm : n = m
    · subst hnm
      simp only [↓reduceIte, Option.some.injEq] at h
      cases h
      exact ⟨o, by simp only [sptAListLookup, hname, if_true]⟩
    · rw [if_neg hnm] at h
      obtain ⟨col, hcol⟩ := sptAListLookup_map_fullCompileSingle t k a c code os hl n p1 p2 h
      exact ⟨col, by simp only [sptAListLookup, hname]; rw [if_neg hnm]; exact hcol⟩

/-- HOL `code_rel_ext_word_to_word` (`word_to_wordProofScript.sml:2155-2183`); HOL's free
    `c2` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_ext_word_to_word"
  (words_as_type_indexed_bitvec)]
theorem code_rel_ext_word_to_word {width : Nat} [NeZero width] (c2 : AsmConfigExact width) :
    ∀ (code : List (Nat × Nat × WordLangProgHOL (BitVec width))) (c1 : Config)
      (col : List (Option (Spt Nat))) (code' : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      compile c1 c2 code = (col, code') → codeRelExt (sptFromAList code) (sptFromAList code') := by
  intro code c1 col code' h
  simp only [compile, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  intro n p1 p2 hl
  rw [sptLookup_sptFromAList] at hl
  obtain ⟨o, ho⟩ := sptAListLookup_map_fullCompileSingle c2.twoRegArith
    (c2.regCount - (5 + c2.avoidRegs.length)) c1.regAlg c2 code _ (compile_zip_length c1 code) n p1 p2
    hl.symm
  exact ⟨_, _, _, _, o, by rw [sptLookup_sptFromAList, ho]⟩

/-- HOL `no_mt_code_rel_ext` (`word_to_wordProofScript.sml:2185-2203`); HOL's free
    `cd1 cd2` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "no_mt_code_rel_ext"
  (words_as_type_indexed_bitvec)]
theorem no_mt_code_rel_ext {width : Nat} [NeZero width]
    (cd1 cd2 : Spt (Nat × WordLangProgHOL (BitVec width))) :
    WordProps.noMtCode cd1 ∧ codeRelExt cd1 cd2 → codeRel cd1 cd2 := by
  rintro ⟨hmt, hext⟩ n ⟨q, r⟩ hl
  obtain ⟨t, k, a, c, col, h⟩ := hext n q r hl.symm
  refine ⟨col, t, k, a, c, ?_⟩
  rw [← h, no_mt_full_compile_single _ t k a c (hmt n q r hl)]

/-- HOL `code_rel_no_share_inst` (`word_to_wordProofScript.sml:2207-2215`); HOL's free
    `op args c1 sz v c2 v'` are explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_no_share_inst"
  (words_as_type_indexed_bitvec)]
theorem code_rel_no_share_inst {width : Nat} [NeZero width] {locWidth : Nat} [NeZero locWidth] {γ : Type}
    (op : Option Nat)
    (args : List (WordLocW locWidth)) (c1 : Spt (Nat × WordLangProgHOL (BitVec width))) (sz : Spt γ)
    (v : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ)
    (c2 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (v' : List (WordLocW locWidth) × WordLangProgHOL (BitVec width) × Option γ) :
    wordSemFindCode op args c1 sz = some v ∧ codeRel c1 c2 ∧
      noShareInstSubprogsHOL v.2.1 = true ∧ wordSemFindCode op args c2 sz = some v' →
    noShareInstSubprogsHOL v'.2.1 = true := by
  simp only [noShareInstSubprogsHOL_eq_notCreated]
  exact code_rel_not_created_subprogs _ op args c1 sz v c2 v'

end Flapjack.Compiler.Backend.WordToWord
