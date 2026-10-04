import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-!
# `word_to_wordProof`: the code relation

The helpers of `compile_single_correct` in
`cakeml/compiler/backend/proofs/word_to_wordProofScript.sml` (159-233):
`code_rel` relates a source code table to its compiled counterpart, entry by
entry through some `compile_single` instance.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CodeRelCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CodeRelCarrier

/-- HOL `rm_perm` (`word_to_wordProofScript.sml:159-163`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "rm_perm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem rm_perm {width : Nat} [NeZero width] {C F : Type} (s : WordSemStateFiniteExact width C F) :
    ({ s with permute := s.permute } : WordSemStateFiniteExact width C F) = s := rfl

/-- `compile_single` keeps the arity component (Flapjack infrastructure,
    inline in HOL's `compile_single_def` reasoning). -/
theorem compileSingle_arity {width : Nat} [NeZero width] (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) (n ar : Nat) (p : WordLangProgHOL (BitVec width))
    (col : Option (Spt Nat)) : (compileSingle t k a c ((n, ar, p), col)).2.1 = ar := rfl

/-- HOL `find_code_thm` (`word_to_wordProofScript.sml:167-189`). Only
    `st.code` and `st.stack_size` of the state occur. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "find_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem find_code_thm {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o1 : Option Nat)
    (o' : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (x : List (WordLocW width)) (args : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (locsize : Option Nat) :
    (∀ n v, sptLookup n st.code = some v →
        ∃ (t : Bool) (k a : Nat) (c : AsmConfigExact width) (col : Option (Spt Nat)),
          sptLookup n l = some (compileSingle t k a c ((n, v), col)).2) ∧
      wordSemFindCode o1 (wordSemAddRetLoc o' x) st.code st.stackSize = some (args, prog, locsize) →
    ∃ (t : Bool) (k a : Nat) (c : AsmConfigExact width) (col : Option (Spt Nat)) (n : Nat)
      (prog' : WordLangProgHOL (BitVec width)),
      (compileSingle t k a c ((n, args.length, prog), col)).2 = (args.length, prog') ∧
        wordSemFindCode o1 (wordSemAddRetLoc o' x) l st.stackSize = some (args, prog', locsize) := by
  rintro ⟨hrel, hfind⟩
  cases o1 with
  | some p =>
    simp only [wordSemFindCode] at hfind ⊢
    cases hp : sptLookup p st.code with
    | none => simp [hp] at hfind
    | some entry =>
      obtain ⟨arity, exp⟩ := entry
      simp only [hp] at hfind
      split at hfind
      · rename_i hlen
        obtain ⟨rfl, rfl, rfl⟩ := by simpa using hfind
        obtain ⟨t, k, a, c, col, hl⟩ := hrel p _ hp
        refine ⟨t, k, a, c, col, p, (compileSingle t k a c ((p, arity, exp), col)).2.2, ?_, ?_⟩
        · rw [hlen]; rfl
        · rw [hl]
          simp [compileSingle_arity, hlen]
      · simp at hfind
  | none =>
    simp only [wordSemFindCode] at hfind ⊢
    split at hfind
    · simp at hfind
    · rename_i hne
      rw [dif_neg hne]
      split at hfind
      · rename_i loc hlast
        cases hp : sptLookup loc st.code with
        | none => simp [hp] at hfind
        | some entry =>
          obtain ⟨arity, exp⟩ := entry
          simp only [hp] at hfind
          split at hfind
          · rename_i hlen
            obtain ⟨rfl, rfl, rfl⟩ := by simpa using hfind
            obtain ⟨t, k, a, c, col, hl⟩ := hrel loc _ hp
            refine ⟨t, k, a, c, col, loc, (compileSingle t k a c ((loc, arity, exp), col)).2.2, ?_, ?_⟩
            · have : (wordSemAddRetLoc o' x).dropLast.length = arity := by
                rw [List.length_dropLast]; omega
              rw [this]; rfl
            · simp only [hl, compileSingle_arity, hlen, if_true]
          · simp at hfind
      · simp at hfind

/-- HOL `pop_env_termdep` (`word_to_wordProofScript.sml:191-195`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "pop_env_termdep"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pop_env_termdep {width : Nat} [NeZero width] {C F : Type}
    (rst x : WordSemStateFiniteExact width C F) (h : popEnv rst = some x) :
    x.termdep = rst.termdep := by
  unfold popEnv at h
  split at h <;> first | (cases h; rfl) | simp at h

/-- Exact HOL `code_rel_def` (`word_to_wordProofScript.sml:198-203`): every
    source code entry is compiled by some `compile_single` instance. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_def"
  (words_as_type_indexed_bitvec)]
def codeRel {width : Nat} [NeZero width] (stc ttc : Spt (Nat × WordLangProgHOL (BitVec width))) :
    Prop :=
  ∀ n v, sptLookup n stc = some v →
    ∃ (col : Option (Spt Nat)) (t : Bool) (k a : Nat) (c : AsmConfigExact width),
      sptLookup n ttc = some (compileSingle t k a c ((n, v), col)).2

/-- HOL `compile_single_eta` (`word_to_wordProofScript.sml:205-210`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_eta"
  (words_as_type_indexed_bitvec)]
theorem compile_single_eta {width : Nat} [NeZero width] (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) (p : Nat) (x : Nat × WordLangProgHOL (BitVec width))
    (y : Option (Spt Nat)) :
    compileSingle t k a c ((p, x), y) = (p, (compileSingle t k a c ((p, x), y)).2) := rfl

/-- First-match lookup through a key-preserving map (Flapjack infrastructure,
    HOL `ALOOKUP_MAP_2` instance). -/
theorem alistLookup_map_compileSingle {width : Nat} [NeZero width] (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) (n : Nat) :
    ∀ ls : List (Nat × Nat × WordLangProgHOL (BitVec width)),
      sptAListLookup n (ls.map (fun p => compileSingle t k a c (p, none))) =
        (sptAListLookup n ls).map (fun v => (compileSingle t k a c ((n, v), none)).2)
  | [] => rfl
  | (m, v) :: ls => by
      simp only [List.map_cons, sptAListLookup]
      by_cases h : n = m
      · subst h
        rw [show compileSingle t k a c ((n, v), none) =
          (n, (compileSingle t k a c ((n, v), none)).2) from rfl]
        simp
      · rw [show compileSingle t k a c ((m, v), none) =
          (m, (compileSingle t k a c ((m, v), none)).2) from rfl]
        simp [h, alistLookup_map_compileSingle t k a c n ls]

/-- HOL `code_rel_union_fromAList` (`word_to_wordProofScript.sml:213-233`);
    HOL's free `t k a c` are the leading binders. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "code_rel_union_fromAList"
  (words_as_type_indexed_bitvec)]
theorem code_rel_union_fromAList {width : Nat} [NeZero width] (t : Bool) (k a : Nat)
    (c : AsmConfigExact width) :
    ∀ (s l : Spt (Nat × WordLangProgHOL (BitVec width)))
      (ls : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      codeRel s l ∧ sptDomain s = sptDomain l →
      codeRel (sptUnion s (sptFromAList ls))
        (sptUnion l (sptFromAList (ls.map (fun p => compileSingle t k a c (p, none))))) := by
  rintro s l ls ⟨hrel, hdom⟩ n v hv
  rw [sptLookup_sptUnion] at hv
  rw [sptLookup_sptUnion]
  cases hs : sptLookup n s with
  | none =>
    rw [hs] at hv
    have hl : sptLookup n l = none := by
      have := congrFun hdom n
      simp only [sptDomain, hs, Option.isSome_none] at this
      cases h : sptLookup n l
      · rfl
      · rw [h] at this; simp at this
    rw [sptLookup_sptFromAList] at hv
    refine ⟨none, t, k, a, c, ?_⟩
    simp [hl, sptLookup_sptFromAList, alistLookup_map_compileSingle, hv]
  | some w =>
    rw [hs] at hv
    cases hv
    obtain ⟨col, t', k', a', c', hl⟩ := hrel n _ hs
    exact ⟨col, t', k', a', c', by simp [hl]⟩

end Flapjack.Compiler.Backend.WordToWord
