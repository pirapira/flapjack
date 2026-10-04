import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Assembly
import Flapjack.Compiler.Backend.WordRemove.Proofs.Correct

/-!
# `word_to_wordProof`: `compile_word_to_word_thm`

`compile_word_to_word_thm` (`word_to_wordProofScript.sml:851-904`): a call of
the start function on the code table compiled by `full_compile_single` (with
`MustTerminate` removed) reproduces every non-error source run, up to a clock
increase and `termdep := 0`, from `compile_single_correct` and
`word_remove_correct`.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
  Flapjack.Compiler.Backend.WordRemove

namespace CompileWordToWordCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileWordToWordCarrier

/-- `full_compile_single` is `compile_single` followed by removing `MustTerminate`
    from the program component (Flapjack infrastructure). -/
theorem fullCompileSingle_eq {width : Nat} [NeZero width] (tt : Bool) (kk aa : Nat)
    (co : AsmConfigExact width) (p : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    fullCompileSingle tt kk aa co p =
      (fun t => (t.1, t.2.1, removeMustTerminate t.2.2)) (compileSingle tt kk aa co p) := rfl

open Classical in
/-- HOL `compile_word_to_word_thm` (`word_to_wordProofScript.sml:851-904`). HOL's free
    `st l cc coracle tt kk aa co start` are explicit; `map (I ## remove_must_terminate) l`
    is the `sptMap` of the reviewed `compile_state`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_word_to_word_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_word_to_word_thm {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (coracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (start : Nat) :
    codeRel st.code l ∧ sptDomain st.code = sptDomain l ∧
      st.compile = (fun conf progs => cc conf (progs.map (fun p => fullCompileSingle tt kk aa co (p, none)))) ∧
      coracle = Prod.map id (List.map (fun p => fullCompileSingle tt kk aa co (p, none))) ∘ st.compileOracle ∧
      Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
    ∃ (perm' : Nat → Nat → Nat) (clk : Nat),
      let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
      let (res, rst) := evaluate prog { st with permute := perm' }
      if res = some .error then True
      else
        let (res1, rst1) := evaluate prog
          { st with
            code := sptMap (fun p => (p.1, removeMustTerminate p.2)) l
            clock := st.clock + clk
            termdep := 0
            compile := cc
            compileOracle := coracle }
        res1 = res ∧ rst1.clock = rst.clock ∧ rst1.ffi = rst.ffi ∧ rst1.stackMax = rst.stackMax := by
  rintro ⟨hrel, hdom, hcomp, rfl, hgc⟩
  let rmt : Nat × Nat × WordLangProgHOL (BitVec width) → Nat × Nat × WordLangProgHOL (BitVec width) :=
    fun t => (t.1, t.2.1, removeMustTerminate t.2.2)
  let cc' : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun conf => cc conf ∘ List.map rmt
  let O' := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle
  have hcomp' : st.compile =
      (fun conf progs => cc' conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) := by
    rw [hcomp]
    funext conf progs
    simp only [cc', Function.comp, List.map_map]
    rfl
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  obtain ⟨perm', H⟩ := compile_single_correct tt kk aa co prog st l O' cc' ⟨hrel, hdom, hcomp', rfl, hgc⟩
  refine ⟨perm', ?_⟩
  rcases hA : evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  rw [hA] at H
  dsimp only at H
  by_cases herr : res = some .error
  · refine ⟨0, ?_⟩
    show (match evaluate prog { st with permute := perm' } with
      | (res, rst) => if res = some .error then True else _)
    rw [hA]
    simp [herr]
  rw [if_neg herr] at H
  rcases hB : evaluate prog { st with code := l, compileOracle := O', compile := cc' } with ⟨res1, rst1⟩
  rw [hB] at H
  dsimp only at H
  obtain ⟨hres, -, -, hs1⟩ := H
  subst hres
  obtain ⟨clk, hW⟩ := word_remove_correct cc prog { st with code := l, compileOracle := O', compile := cc' }
    res1 rst1 ⟨hB, rfl, herr⟩
  refine ⟨clk, ?_⟩
  have hst : ({ st with
      code := sptMap (fun p => (p.1, removeMustTerminate p.2)) l
      clock := st.clock + clk
      termdep := 0
      compile := cc
      compileOracle := Prod.map id (List.map (fun p => fullCompileSingle tt kk aa co (p, none))) ∘
        st.compileOracle } : WordSemStateFiniteExact width C F) =
      compileState clk cc { st with code := l, compileOracle := O', compile := cc' } := by
    simp only [compileState]
    congr 1
    funext k
    simp only [O', Function.comp, Prod.map, List.map_map, id]
    rfl
  show (match evaluate prog { st with permute := perm' } with
    | (res, rst) => if res = some .error then True else _)
  rw [hA]
  dsimp only
  rw [if_neg herr, hst, show (WordLangProgHOL.call none (some start) [0] none : WordLangProgHOL (BitVec width)) =
    removeMustTerminate prog from rfl, hW]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> rw [hs1] <;> rfl

end Flapjack.Compiler.Backend.WordToWord
