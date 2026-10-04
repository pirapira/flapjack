import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.MemoryLoad
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.MemoryStore

namespace Flapjack.WordToStackProofs.InstSimulation.Memory
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

/-- Whole original Mem case, including every memory opcode and all five guards.
The unsupported 16-bit cases contradict actual source success, as in HOL;
no additional opcode restriction is assumed. All native runs, full relations
and resource conclusions are retained. Evaluators inherit reals_as_rational_cuts. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstMemory {width : Nat} [NeZero width] {C F : Type}
    (operation : WordMemOp) (ac : AsmConfigExact width) (valueRegister base k f frame : Nat) (offset : BitVec width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.mem operation valueRegister (.addr base offset)) source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar (.mem operation valueRegister (.addr base offset)))
    (bound : maxVarInstHOL (.mem operation valueRegister (.addr base offset)) < 2*frame+2*k)
    (convention : instArgConventionExact (.mem operation valueRegister (.addr base offset)))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.mem operation valueRegister (.addr base offset)) (k,f,frame),target) =
        (none,post) ∧ stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  cases operation with
  | load =>
    exact MemoryLoad.evaluateWInstLoad ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | load8 =>
    exact MemoryLoad.evaluateWInstLoad8 ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | load32 =>
    exact MemoryLoad.evaluateWInstLoad32 ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | store =>
    exact MemoryStore.evaluateWInstStore ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | store8 =>
    exact MemoryStore.evaluateWInstStore8 ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | store32 =>
    exact MemoryStore.evaluateWInstStore32 ac valueRegister base k f frame offset source sourcePost target lens
      executed physical bound convention related
  | load16 => simp [WordSemStateFiniteExact.inst] at executed
  | store16 => simp [WordSemStateFiniteExact.inst] at executed

end Flapjack.WordToStackProofs.InstSimulation.Memory
