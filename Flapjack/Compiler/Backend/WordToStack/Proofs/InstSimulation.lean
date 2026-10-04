import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Arithmetic
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Constant
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Memory
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Skip
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.FpArith
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.FpTransfer
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.FpConversions

namespace Flapjack.WordToStackProofs.InstSimulation
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

/-- Whole original FP family with all sixteen native opcodes, both transfer
width regimes and packed conversions. Every original guard and the full actual
native evaluation/state relation/stack-resource existential is retained.
Evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFp {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (operation : HolFp) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp operation) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.fp operation : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.fp operation : WordLangInst (BitVec width)) < 2*frame+2*k)
    (convention : instArgConventionExact (.fp operation : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp operation) (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  cases operation with
  | fpLess d0 d1 d2 =>
    exact FpArith.evaluateWInstFpLess ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpLessEqual d0 d1 d2 =>
    exact FpArith.evaluateWInstFpLessEqual ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpEqual d0 d1 d2 =>
    exact FpArith.evaluateWInstFpEqual ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpAbs d0 d1 =>
    exact FpArith.evaluateWInstFpAbs ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpNeg d0 d1 =>
    exact FpArith.evaluateWInstFpNeg ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpSqrt d0 d1 =>
    exact FpArith.evaluateWInstFpSqrt ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpAdd d0 d1 d2 =>
    exact FpArith.evaluateWInstFpAdd ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpSub d0 d1 d2 =>
    exact FpArith.evaluateWInstFpSub ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpMul d0 d1 d2 =>
    exact FpArith.evaluateWInstFpMul ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpDiv d0 d1 d2 =>
    exact FpArith.evaluateWInstFpDiv ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpFma d0 d1 d2 =>
    exact FpArith.evaluateWInstFpFma ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpMov d0 d1 =>
    exact FpArith.evaluateWInstFpMov ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpMovToReg d0 d1 d2 =>
    exact FpTransfer.evaluateWInstFpMovToReg ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpMovFromReg d0 d1 d2 =>
    exact FpTransfer.evaluateWInstFpMovFromReg ac d0 d1 d2 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpToInt d0 d1 =>
    exact FpConversions.evaluateWInstFpToInt ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related
  | fpFromInt d0 d1 =>
    exact FpConversions.evaluateWInstFpFromInt ac d0 d1 k f frame source sourcePost target lens
      executed physical bound convention related

/-- Complete original evaluate_wInst, over every native instruction.
WordSem consumes the reviewed constructor-for-constructor instruction codec;
no opcode, width, alias, spill or error-path restriction is added. The original
five guards establish the actual compiled target evaluation, full state relation
and stack resources. Every case is proved internally, with no supplied target
run or case-simulation hypothesis. The evaluators inherit
reals_as_rational_cuts (SOUNDNESS item 8); canonical maps and word dimensions
are explicitly qualified. This theorem does not complete comp_correct or the
whole compiler refinement. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (instruction : HolInst width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst instruction.toWordLangInst source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar instruction.toWordLangInst)
    (bound : maxVarInstHOL instruction.toWordLangInst < 2*frame+2*k)
    (convention : instArgConventionExact instruction)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative instruction (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  cases instruction with
  | skip =>
    exact Skip.evaluateWInstSkip ac k f frame source sourcePost target lens
      executed physical bound convention related
  | const destination value =>
    exact Constant.evaluateWInstConst ac destination k f frame value
      source sourcePost target lens executed physical bound convention related
  | arith operation =>
    exact Arithmetic.evaluateWInstArith ac operation k f frame source sourcePost target lens
      executed physical bound convention related
  | mem operation register address =>
    cases address with
    | addr base offset =>
      exact Memory.evaluateWInstMemory operation ac register base k f frame offset
        source sourcePost target lens executed physical bound convention related
  | fp operation =>
    exact evaluateWInstFp ac operation k f frame source sourcePost target lens
      executed physical bound convention related

end Flapjack.WordToStackProofs.InstSimulation
