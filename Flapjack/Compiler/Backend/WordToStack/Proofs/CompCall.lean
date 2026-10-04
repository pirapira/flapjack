import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly

namespace Flapjack.WordToStackProofs.CompCall
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs.CompCorrect

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

/-- Canonical StackSem codec for the owning target carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original local evaluate_Seq_Skip (10074-10078): a leading native Skip does
not change the evaluation pair, for arbitrary program and state. The evaluator
closure inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_Seq_Skip"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateSeqSkip {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq .skip p, s) = StackSemEvaluate.evaluate (p, s) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
  simp [StackSemControl.fixClock]

/-- Original local comp_Call (10090-10114): the specialization of the full
comp_correct to the top-level entry call (comp_Call_lemma, 10080) at k with
frame 0/0, bitmap position LENGTH t.bitmaps and empty bitmap list. All original
premises (actual source Call run, error-free result, state_rel ... 0 0 ... 0)
and the full conclusion (target clock existential and run, 1w ≠ 0w, 2w ≠ 0w,
and the conditional FFI/clock or Halt-2/io-prefix/stack-limit branch) are
retained. The compiled entry is Seq Skip (Call NONE (INL start) NONE), removed
by evaluate_Seq_Skip; the result-specific post-relations of comp_correct give
the FFI and clock equalities. Canonical maps and word widths are qualified;
the evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_Call"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (start : Nat) (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
      (t : StackSemStateFiniteExact width C F) (lens : List Nat),
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k 0 0 s t lens 0 →
      ∃ (ck : Nat) (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
        StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
          (res1, t1) ∧ (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
        (open Classical in if res.map compileResult = res1 then s1.ffi = t1.ffi ∧ s1.clock = t1.clock
         else res1 = some (.halt (.word 2)) ∧ List.IsPrefix t1.ffi.ioEvents s1.ffi.ioEvents ∧
           s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit) := by
  intro start s k res s1 t lens ⟨run, notError, related⟩
  have kBound : 4 < k := related.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ck, t1, res1, targetRun, resultRel⟩ :=
    CompCorrect.compCorrect ac (.call none (some start) [0] none) s k 0 0 s1 t res
      .nil .nil t.bitmaps.length t.bitmaps.length (.seq .skip (.call none (.inl start) none)) lens
      ⟨run, notError, related, by simp [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, isPhyVar], by simp [flatExpConventions], by
        simp [compNative, callDestNative, seqStackFreeNative, Compiler.Backend.WordToStack.stackFree],
        by simp [appListAppend, appendAux], by simp [appListAppend, appendAux], by simp [appListAppend, appendAux],
        by simp [StackSem.getLabelsExact], by simp [maxVarHOL, maxList]; omega⟩
  have wide : 8 ≤ width := by
    unfold stateRel at related
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩ := related
    exact h
  have oneLt : 1 < 2 ^ width := Nat.one_lt_two_pow (by omega)
  have twoLt : 2 < 2 ^ width :=
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) wide
  refine ⟨ck, t1, res1, (evaluateSeqSkip _ _).symm.trans targetRun, ?_, ?_, ?_⟩
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt oneLt] at this
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt twoLt] at this
  · unfold compCorrectResult at resultRel
    by_cases same : res.map compileResult = res1
    · rw [if_pos same]
      rw [if_neg (not_not.mpr same)] at resultRel
      have ffiClock : ∀ {f frame lens' extra} {s' : WordSemStateFiniteExact width (Nat × C) F},
          stateRel ac k f frame s' t1 lens' extra → s'.ffi = t1.ffi ∧ s'.clock = t1.clock :=
        fun rel => ⟨rel.2.2.2.1.symm, rel.1⟩
      rcases res with _ | r
      · exact ffiClock resultRel
      · cases r with
        | result _ values => exact ffiClock resultRel.1
        | exception _ value =>
          obtain ⟨nonGc, gc, rel, _, _⟩ := resultRel
          exact ffiClock (s' := pushLocals nonGc gc s1) rel
        | «break» _ => exact ffiClock resultRel
        | «continue» _ => exact ffiClock resultRel
        | _ => exact resultRel
    · rw [if_neg same]
      rw [if_pos same] at resultRel
      exact resultRel

end Flapjack.WordToStackProofs.CompCall
