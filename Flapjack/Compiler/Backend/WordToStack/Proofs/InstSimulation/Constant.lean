import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.WordToStackProofs.InstSimulation.Constant
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

/-- The Const branch (4705–4714) of the full original evaluate_wInst.
All five original guards and every result conjunct are retained. The actual
register/stack write is derived through the reviewed native continuation law;
there is no target-execution or final-relation premise. The source instruction
is constructor-for-constructor Const on WordLangInst, and the compiled Const
is on HolInst, both at the same positive word width. The evaluators inherit
reals_as_rational_cuts (SOUNDNESS item 8), without an independent agreement claim.
The full arbitrary-instruction theorem remains open on its other cases. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstConst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register k f frame : Nat) (word : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.const register word) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.const register word))
    (bound : maxVarInstHOL (.const register word) < 2 * frame + 2 * k)
    (_convention : instArgConventionExact (.const register word))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.const register word) (k,f,frame), target) =
        (none, post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have even : register % 2 = 0 := by simpa [everyVarInstHOL, isPhyVar] using physical
  have range : register < 2 * frame + 2 * k := bound
  have sourceEq : WordSemStateFiniteExact.setVar register (.word word) source = sourcePost := by
    simpa [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign,
      WordSemStateFiniteExact.wordExp] using executed
  rcases compiled : wReg1 register (k,f,frame) with ⟨loads, reg⟩
  obtain ⟨post, run, postRel, lengthEq, spaceEq⟩ :=
    StoreRegister.evaluateWStackStoreWReg1 ac register reg k f frame loads source target lens
      (.word word) target.stack.length target.stackSpace compiled even range related rfl rfl
  refine ⟨post, ?_, sourceEq ▸ postRel, lengthEq, spaceEq⟩
  simp only [wInstNative, StoreRegister.evaluateWRegWrite1Seq, compiled]
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  simpa [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp] using run

end Flapjack.WordToStackProofs.InstSimulation.Constant
