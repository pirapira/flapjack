import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelSemantics
import Flapjack.Compiler.Backend.WordToStack.Proofs.InitializationStateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Misc.Sptree.ToAList

namespace Flapjack.WordToStackProofs.CompileSemantics
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.WordToStackProofs.InitializationStateRel

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- ALOOKUP of the Spt association-list lookup (Flapjack transport). -/
private theorem sptAListLookup_eq {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

private theorem mem_of_lookup {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho
        simp only [decide_true, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [ho, decide_false, Bool.false_eq_true, if_false] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- Full original compile_semantics (10709-10758): for the native top-level
compiler at perf = F, the original code-table, register-count, init_state_ok,
stub-freeness, bitmap-prefix, conventions and non-Fail premises give the
target semantics in extend_with_resource_limit' (word_lang_safe_for_space of
the initial source state) of the singleton source semantics. As in HOL the
whole state relation of make_init is init_state_ok_IMP_state_rel, whose code
premises come from compile_word_to_stack_IMP_ALOOKUP and
MAP_FST_compile_word_to_stack, and the two precision cases are
state_rel_IMP_semantics' and state_rel_IMP_semantics. HOL's EVERY over the
code list is a membership quantifier, its singleton set the predicate
fun b => b = semantics ..., and the boolean word_lang_safe_for_space is
decided classically. Canonical maps and word widths are qualified; evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_semantics"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileSemantics {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start : Nat)
    (h : t.code = sptFromAList (compileNative asmConf false code).2.2.2 ∧
      k = asmConf.regCount - (5 + asmConf.avoidRegs.length) ∧
      initStateOk asmConf k t coracle ∧
      panPropsALookupEq raiseStubLocation code = none ∧
      panPropsALookupEq storeConstsStubLocation code = none ∧
      (compileNative asmConf false code).1 <+: t.bitmaps ∧
      (∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
        postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
          entry.2.2 = true) ∧
      WordSemStateFiniteExact.semantics (makeInit asmConf k t (sptFromAList code) coracle) start ≠
        .fail) :
    open Classical in
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (decide (WordSemStateFiniteExact.wordLangSafeForSpace
        (makeInit asmConf k t (sptFromAList code) coracle) start))
      (fun b => b =
        WordSemStateFiniteExact.semantics (makeInit asmConf k t (sptFromAList code) coracle) start)
      (StackSemEvaluate.semantics start t) := by
  classical
  obtain ⟨codeEq, kEq, ok, noRaise, noStore, bitmapsPrefix, conventions, notFail⟩ := h
  subst kEq
  rcases compiled : compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [compileNative, Bool.false_eq_true, if_false, compiled] at codeEq bitmapsPrefix
  have keys := mapFstCompileWordToStack asmConf false _ code (.list [4], 1) bodies
    (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  have related : stateRel asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) 0 0
      (makeInit asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t (sptFromAList code)
        coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
    apply initStateOkImpliesStateRel
    refine ⟨?_, ?_, ?_, ?_, ok⟩
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq]
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq, stubsDistinct]
    · intro n wordProg argumentCount lookup
      rw [sptLookup_sptFromAList, sptAListLookup_eq] at lookup
      have member := mem_of_lookup lookup
      obtain ⟨flat, allocated⟩ := conventions _ member
      obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
        compileWordToStackImpALookup asmConf false _ code (.list [4]) 1 bodies frames output
          nextIndex n argumentCount wordProg t.bitmaps compiled lookup
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
          (by simpa [appListAppend, appendAux] using bitmapsPrefix)
      refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
      have notRaise : n ≠ raiseStubLocation := by
        rintro rfl
        rw [noRaise] at lookup
        cases lookup
      have notStore : n ≠ storeConstsStubLocation := by
        rintro rfl
        rw [noStore] at lookup
        cases lookup
      rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq]
      simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
    · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
      funext x
      simp only [List.map_cons, List.mem_cons, keys]
  by_cases safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (makeInit asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t
        (sptFromAList code) coracle) start
  · simp only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, decide_eq_true safe, if_true]
    exact StateRelSemantics.stateRelImpSemantics' asmConf _ _ t [] start ⟨related, notFail, safe⟩
  · simp only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, decide_eq_false safe,
      Bool.false_eq_true, if_false]
    exact StateRelSemantics.stateRelImpSemantics asmConf _ _ t [] start ⟨related, notFail⟩

end Flapjack.WordToStackProofs.CompileSemantics
