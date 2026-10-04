import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation

namespace Flapjack.WordToStackProofs.CompCorrect.Inst
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

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

/-- The source-side argument convention of an instruction is the exact
convention of its native carrier (Flapjack codec transport, no HOL original). -/
private theorem instArgConvention_ofWordLangInst {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    instArgConvention i = instArgConventionExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | ⟨_, _⟩ | ⟨a⟩ | ⟨_, _, _⟩ | ⟨_⟩
  all_goals try rfl
  rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  all_goals (cases ri <;> rfl)

/-- Full original comp_correct Inst case (6315-6326) of comp_correct5756 /
motive5719-5751: the entire Seq.Simulation motive with all original
hypotheses and the full existential target-run/resource/result conclusion.
As in HOL, the source run succeeds with NONE, post_alloc_conventions supplies
every_var_inst is_phy_var and inst_arg_convention, max_var gives the
max_var_inst bound, and the full original evaluate_wInst supplies the target
run with ck = 0. The source WordLangInst is compiled through the reviewed
HolInst codec. Canonical maps and word widths are qualified; the evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.inst i) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, _flat,
    compilation, _lengthBound, _bitmapBound, _bitmapPrefix, _labels, maxBound⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases instRun : WordSemStateFiniteExact.inst i source with _ | post
  · rw [instRun] at execution
    obtain ⟨rfl, -⟩ := Prod.mk.inj execution
    exact absurd rfl notError
  · rw [instRun] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    have conventionParts := conventions
    simp only [postAllocConventionsHOL, everyVarHOL, callArgConventionHOL,
      Bool.and_eq_true] at conventionParts
    obtain ⟨physical, _, convention⟩ := conventionParts
    simp only [compNative, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -⟩ := compilation
    obtain ⟨post', run, postRel, _, _⟩ :=
      InstSimulation.evaluateWInst ac (HolInst.ofWordLangInst i) k f frame source post
        target lens (by simpa only [HolInst.to_of] using instRun)
        (by simpa only [HolInst.to_of] using physical)
        (by simpa only [HolInst.to_of, maxVarHOL] using maxBound)
        (by rw [← instArgConvention_ofWordLangInst]; exact convention) related
    refine ⟨0, post', none, by simpa using run, ?_⟩
    simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, if_false]
    exact postRel

end Flapjack.WordToStackProofs.CompCorrect.Inst
