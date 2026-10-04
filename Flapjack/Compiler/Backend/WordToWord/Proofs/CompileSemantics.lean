import Flapjack.Compiler.Backend.WordToWord.Proofs.NoInstallCompileSingle
import Flapjack.Compiler.Backend.Semantics.WordSem.Semantics
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

/-!
# `word_to_wordProof`: Pancake-facing semantics preservation

`panLang_compile_word_to_word_thm` (`word_to_wordProofScript.sml:2219-2265`)
and `word_to_word_compile_semantics` (2267-2489): `word_to_word$compile`
preserves the `wordSem` semantics of a start call on a code table without
`Install`, `Alloc` or `MustTerminate`. HOL proves the latter by comparing the
clocked runs case by case with `evaluate_add_clock`; here every clocked run of
the two states agrees on its result and FFI state (`compile_runs_agree`), and
`semantics` reads its runs only through these (`semantics_eq_of_runs`).
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps Flapjack.Compiler.Encoders.Asm

namespace CompileSemanticsCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSemanticsCarrier

open Classical in
/-- HOL `panLang_compile_word_to_word_thm` (`word_to_wordProofScript.sml:2219-2265`). HOL's
    free `st l start` are explicit; HOL's existential `clk` does not occur in the body and
    is kept. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "panLang_compile_word_to_word_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem panLang_compile_word_to_word_thm {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (start : Nat) :
    codeRel st.code l ∧ noInstallCode st.code ∧ noAllocCode st.code ∧ noMtCode st.code ∧
      sptDomain st.code = sptDomain l ∧ Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
    ∃ (perm' : Nat → Nat → Nat) (_clk : Nat),
      let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
      let (res, rst) := evaluate prog { st with permute := perm' }
      if res = some .error then True
      else
        let (res1, rst1) := evaluate prog { st with code := l }
        res1 = res ∧ rst1.clock = rst.clock ∧ rst1.ffi = rst.ffi ∧ rst1.stackMax = rst.stackMax := by
  rintro ⟨hrel, hnic, hnac, -, hdom, hgc⟩
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  obtain ⟨perm', H⟩ := no_install_no_alloc_compile_single_correct prog st l
    ⟨hrel, rfl, rfl, hnic, hnac, hdom, hgc⟩
  refine ⟨perm', 0, ?_⟩
  dsimp only at H ⊢
  rcases hS : evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  rw [hS] at H
  dsimp only at H ⊢
  by_cases herr : res = some .error
  · simp [herr]
  rw [if_neg herr] at H ⊢
  rcases hT : evaluate prog { st with code := l } with ⟨res1, rst1⟩
  rw [hT] at H
  dsimp only at H ⊢
  obtain ⟨hres, -, -, heq⟩ := H
  refine ⟨hres, ?_, ?_, ?_⟩ <;> rw [heq]

open Classical in
/-- Every clocked start call that does not fail on the source state gives the same
    result and FFI state on the compiled code table (Flapjack infrastructure: HOL's
    combination of `panLang_compile_word_to_word_thm` and `permute_swap_lemma3` in each
    case of `word_to_word_compile_semantics`). -/
theorem compile_runs_agree {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (start k : Nat) (hrel : codeRel s.code l) (hnic : noInstallCode s.code)
    (hnac : noAllocCode s.code) (hnmc : noMtCode s.code) (hdom : sptDomain s.code = sptDomain l)
    (hgc : Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (hstack : s.stack = [])
    (hne : (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ≠ some .error) :
    (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).1 =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ∧
      (evaluate (.call none (some start) [0] none) { s with clock := k, code := l }).2.ffi =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.ffi := by
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  let sk : WordSemStateFiniteExact width C F := { s with clock := k }
  obtain ⟨perm', -, H⟩ := panLang_compile_word_to_word_thm sk l start
    ⟨hrel, hnic, hnac, hnmc, hdom, hgc⟩
  have P3 := permute_swap_lemma3 prog sk perm' []
  rcases hE : evaluate prog sk with ⟨q, r⟩
  change (evaluate prog sk).1 ≠ some .error at hne
  rw [hE] at hne P3
  dsimp only at hne P3
  obtain ⟨perm'', stack', hP, -⟩ := P3 ⟨hne, hnac, rfl, hnic, rfl, by
    intro fr hfr
    change fr ∈ s.stack at hfr
    rw [hstack] at hfr
    cases hfr⟩
  dsimp only at H
  rw [hP] at H
  dsimp only at H
  rw [if_neg hne] at H
  rcases hT : evaluate prog { sk with code := l } with ⟨q1, r1⟩
  rw [hT] at H
  dsimp only at H
  obtain ⟨h1, -, h3, -⟩ := H
  exact ⟨h1, h3⟩

/-- The failure test of `semantics` on a clocked run's result (Flapjack infrastructure,
    the first `case` of HOL `semantics_def`). -/
def semFailCond {width : Nat} [NeZero width] : Option (WordSemResult width) → Prop
  | some (.exception _ _) => True
  | some (.result ret _) => ret ≠ WordLocW.loc 1 0
  | some .error => True
  | none => True
  | _ => False

/-- The terminating-outcome relation of `semantics` (Flapjack infrastructure, the
    second `case` of HOL `semantics_def`). -/
def semTermOutcome {width : Nat} [NeZero width] : Option (WordSemResult width) → HolOutcome → Prop
  | some (.finalFfi e), outcome => outcome = HolOutcome.ffiOutcome e
  | some (.result _ _), outcome => outcome = HolOutcome.success
  | some .notEnoughSpace, outcome => outcome = HolOutcome.resourceLimitHit
  | _, _ => False

open Classical in
/-- The body of HOL `semantics_def` over a family of clocked runs (Flapjack infrastructure). -/
noncomputable def semBody {width : Nat} [NeZero width] {C F : Type}
    (E : Nat → Option (WordSemResult width) × WordSemStateFiniteExact width C F) : HolBehaviour :=
  if ∃ k, semFailCond (E k).1 then .fail
  else
    match holOptionSome (fun res => ∃ k t r outcome,
        E k = (r, t) ∧ semTermOutcome r outcome ∧ res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
    | some res => res
    | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
        l = HolLList.fromList (E k).2.ffi.ioEvents))

theorem semantics_eq_body {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (start : Nat) :
    semantics s start = semBody (fun k => evaluate (.call none (some start) [0] none) { s with clock := k }) :=
  rfl

/-- `semantics` reads its clocked runs only through their results and FFI states
    (Flapjack infrastructure). -/
theorem semantics_eq_of_runs {width : Nat} [NeZero width] {C F : Type}
    (s t : WordSemStateFiniteExact width C F) (start : Nat)
    (A : ∀ k, (evaluate (.call none (some start) [0] none) { t with clock := k }).1 =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ∧
      (evaluate (.call none (some start) [0] none) { t with clock := k }).2.ffi =
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.ffi) :
    semantics s start = semantics t start := by
  rw [semantics_eq_body s start, semantics_eq_body t start]
  have hc : (∃ k, semFailCond (evaluate (.call none (some start) [0] none)
        { s with clock := k }).1) ↔
      (∃ k, semFailCond (evaluate (.call none (some start) [0] none) { t with clock := k }).1) :=
    exists_congr fun k => by rw [(A k).1]
  have hsome : (fun res => ∃ k t' r outcome,
        evaluate (.call none (some start) [0] none) { s with clock := k } = (r, t') ∧
        semTermOutcome r outcome ∧ res = HolBehaviour.terminate outcome t'.ffi.ioEvents) =
      (fun res => ∃ k t' r outcome,
        evaluate (.call none (some start) [0] none) { t with clock := k } = (r, t') ∧
        semTermOutcome r outcome ∧ res = HolBehaviour.terminate outcome t'.ffi.ioEvents) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t', r, outcome, he, hm, hr⟩
      refine ⟨k, (evaluate (.call none (some start) [0] none) { t with clock := k }).2, r, outcome,
        Prod.ext (by rw [(A k).1, he]) rfl, hm, ?_⟩
      rw [hr, (A k).2, he]
    · rintro ⟨k, t', r, outcome, he, hm, hr⟩
      refine ⟨k, (evaluate (.call none (some start) [0] none) { s with clock := k }).2, r, outcome,
        Prod.ext (by rw [← (A k).1, he]) rfl, hm, ?_⟩
      rw [hr, ← (A k).2, he]
  have hdiv : (fun l => ∃ k, l = HolLList.fromList
        (evaluate (.call none (some start) [0] none) { s with clock := k }).2.ffi.ioEvents) =
      (fun l => ∃ k, l = HolLList.fromList
        (evaluate (.call none (some start) [0] none) { t with clock := k }).2.ffi.ioEvents) := by
    funext l
    exact propext (exists_congr fun k => by rw [(A k).2])
  unfold semBody
  by_cases hf : ∃ k, semFailCond (evaluate (.call none (some start) [0] none)
      { s with clock := k }).1
  · rw [if_pos hf, if_pos (hc.mp hf)]
  · rw [if_neg hf, if_neg (mt hc.mpr hf), hsome, hdiv]

/-- Membership of a key is unchanged by the entry-wise `full_compile_single` of
    `compile` (Flapjack infrastructure for HOL's `domain_fromAList`/`MAP_ZIP` step). -/
theorem sptAListLookup_isSome_map_fullCompileSingle {width : Nat} [NeZero width] (t : Bool)
    (k a : Nat) (c : AsmConfigExact width) :
    ∀ (code : List (Nat × Nat × WordLangProgHOL (BitVec width))) (os : List (Option (Spt Nat))),
      os.length = code.length → ∀ n,
      (sptAListLookup n ((code.zip os).map (fullCompileSingle t k a c))).isSome =
        (sptAListLookup n code).isSome
  | [], _, _, _ => by simp [sptAListLookup]
  | _ :: _, [], hl, _ => by simp at hl
  | (m, ar, p) :: code, o :: os, hl, n => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.zip_cons_cons, List.map_cons]
    have hname : (fullCompileSingle t k a c ((m, ar, p), o)).1 = m := rfl
    simp only [sptAListLookup, hname]
    by_cases hnm : n = m
    · simp only [hnm, if_true, Option.isSome_some]
    · simp only [hnm, if_false]
      exact sptAListLookup_isSome_map_fullCompileSingle t k a c code os hl n

open Classical in
/-- HOL `word_to_word_compile_semantics` (`word_to_wordProofScript.sml:2267-2489`). HOL's free
    `wconf acomf wprog0 col wprog s start t` are explicit, in order of appearance; the
    commented-out HOL premises are absent, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "word_to_word_compile_semantics"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_to_word_compile_semantics {width : Nat} [NeZero width] {C F : Type}
    (wconf : Config) (acomf : AsmConfigExact width)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width))) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width C F) (start : Nat) (t : WordSemStateFiniteExact width C F) :
    compile wconf acomf wprog0 = (col, wprog) ∧
      Compiler.Backend.WordSimp.gcFunConstOk s.gcFun ∧
      noInstallCode (sptFromAList wprog0) ∧ noAllocCode (sptFromAList wprog0) ∧
      noInstallCode s.code ∧ noAllocCode s.code ∧ noMtCode (sptFromAList wprog0) ∧
      (wprog0.map Prod.fst).Nodup ∧ s.stack = [] ∧
      t.code = sptFromAList wprog ∧ sptLookup 0 t.locals = some (.loc 1 0) ∧
      t = { s with code := t.code } ∧ s.code = sptFromAList wprog0 ∧
      semantics s start ≠ .fail →
    semantics s start = semantics t start := by
  rintro ⟨hcomp, hgc, -, -, hnic, hnac, hnmc, -, hstack, htc, -, ht, hsc, hnf⟩
  have hext := code_rel_ext_word_to_word acomf wprog0 wconf col wprog hcomp
  have hrel0 := no_mt_code_rel_ext _ _ ⟨hnmc, hext⟩
  have hdom0 : sptDomain (sptFromAList wprog0) = sptDomain (sptFromAList wprog) := by
    simp only [compile, Prod.mk.injEq] at hcomp
    obtain ⟨-, rfl⟩ := hcomp
    funext n
    simp only [sptDomain, sptLookup_sptFromAList]
    rw [sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ wprog0 _ (compile_zip_length wconf wprog0)]
  rw [htc] at ht
  subst ht
  rw [← hsc] at hrel0 hdom0 hnmc
  have hne : ∀ k, (evaluate (.call none (some start) [0] none) { s with clock := k }).1 ≠
      some .error := by
    intro k he
    apply hnf
    unfold semantics
    dsimp only
    rw [if_pos ⟨k, by rw [he]; trivial⟩]
  apply semantics_eq_of_runs
  intro k
  exact compile_runs_agree s (sptFromAList wprog) start k hrel0 hnic hnac hnmc hdom0 hgc hstack (hne k)

end Flapjack.Compiler.Backend.WordToWord
