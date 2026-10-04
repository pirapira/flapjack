import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.MemoryLoad
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.MemoryStore

namespace Flapjack.WordToStackProofs.InstSimulation.Skip
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

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

/-- Full original Skip case with all five original guards and complete actual
native run/stateRel/resource conclusion. The evaluator dependency inherits
reals_as_rational_cuts; this case establishes no numerical FP agreement. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst .skip source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar (WordLangInst.skip : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (WordLangInst.skip : WordLangInst (BitVec width)) < 2*frame+2*k)
    (_convention : instArgConventionExact (HolInst.skip : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative .skip (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have sourceSame : source = sourcePost := by
    simpa [WordSemStateFiniteExact.inst] using executed
  subst sourcePost
  refine ⟨target, ?_, related, rfl, rfl⟩
  simp [wInstNative, StackSemEvaluate.evaluate_inst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger]

end Flapjack.WordToStackProofs.InstSimulation.Skip
