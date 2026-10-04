import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Binary
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Shift
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Division
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.LongArithmetic

namespace Flapjack.WordToStackProofs.InstSimulation.Arithmetic
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

/-- Full original evaluate_wInst Arith family, over every native opcode and
both register/immediate operand forms. The source instruction uses the reviewed
constructor-for-constructor codec to WordSem's instruction carrier. All five
original guards, the actual target existential, complete relation and stack
resources are retained; the constituent full cases supply the proof.
Canonical finite maps and positive word dimensions are qualified; evaluator
closure inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstArith {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (arith : HolArith width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.arith arith.toWordLangArith) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar
      (.arith arith.toWordLangArith : WordLangInst (BitVec width)))
    (bound : maxVarInstHOL (.arith arith.toWordLangArith : WordLangInst (BitVec width)) < 2*frame+2*k)
    (convention : instArgConventionExact (.arith arith : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.arith arith) (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  cases arith <;> try cases ‹HolRegImm width›
  all_goals first
    | exact Binary.evaluateWInstBinopReg ac _ _ _ k f frame _ source sourcePost target lens executed physical bound convention related
    | exact Binary.evaluateWInstBinopImm ac _ _ _ k f frame _ source sourcePost target lens executed physical bound convention related
    | exact Shift.evaluateWInstShiftReg ac _ _ _ k f frame _ source sourcePost target lens executed physical bound convention related
    | exact Shift.evaluateWInstShiftImm ac _ _ _ k f frame _ source sourcePost target lens executed physical bound convention related
    | exact Division.evaluateWInstDiv ac _ _ _ k f frame source sourcePost target lens executed physical bound convention related
    | exact LongArithmetic.evaluateWInstLongMul ac _ _ _ _ k f frame source sourcePost target lens executed physical bound convention related
    | exact LongArithmetic.evaluateWInstLongDiv ac _ _ _ _ _ k f frame source sourcePost target lens executed physical bound convention related
    | exact CarryOverflow.evaluateWInstCarry ac _ _ _ _ k f frame source sourcePost target lens executed physical bound convention related
    | exact CarryOverflow.evaluateWInstAddOverflow ac _ _ _ _ k f frame source sourcePost target lens executed physical bound convention related
    | exact CarryOverflow.evaluateWInstSubOverflow ac _ _ _ _ k f frame source sourcePost target lens executed physical bound convention related
end Flapjack.WordToStackProofs.InstSimulation.Arithmetic
