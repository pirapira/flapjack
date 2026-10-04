import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelFp

namespace Flapjack.WordToStackProofs.InstSimulation.FpConversions
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


/-- Full original evaluate_wInst FPToInt case: all five original guards,
actual native evaluation existential, full state relation and stack resources.
Keeps arbitrary positive widths, width64 and packed non64 branches, odd/even
half selection and round-ties-to-even conversion. Definedness and range checks
come from source execution; target reads and updates are derived internally.
Canonical maps and words are qualified; both evaluators inherit
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpToInt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination input k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpToInt destination input)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar
      (.fp (.fpToInt destination input) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpToInt destination input) : WordLangInst (BitVec width)) < 2*frame+2*k)
    (_convention : instArgConventionExact (.fp (.fpToInt destination input) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpToInt destination input)) (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have reads : ∀ n, StackSemStateOps.getFpVar n target = WordSemStateFiniteExact.getFpVar n source :=
    fun n => (StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related).symm
  simp only [WordSemStateFiniteExact.inst] at executed
  repeat' (first | contradiction | split at executed)
  all_goals simp only [Option.some.injEq] at executed
  all_goals subst sourcePost
  all_goals refine ⟨_, ?_, StateRelFp.stateRelSetFpVar ac k f frame source target lens 0 _ _ related, rfl, rfl⟩
  all_goals simp_all [wInstNative,StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
    StackSemFpInstructions.instFp,StackSemFpRegisterInstructions.instFpRegister,
    StackSemFpRegisterInstructions.instFpToInt]

/-- Full original evaluate_wInst FPFromInt case: all five original guards,
actual native evaluation existential, full state relation and stack resources.
Keeps arbitrary positive widths, width64 and packed non64 branches, odd/even
half selection and round-ties-to-even conversion. Definedness and range checks
come from source execution; target reads and updates are derived internally.
Canonical maps and words are qualified; both evaluators inherit
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wInst"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWInstFpFromInt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (destination input k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst (.fp (.fpFromInt destination input)) source = some sourcePost)
    (_physical : everyVarInstHOL isPhyVar
      (.fp (.fpFromInt destination input) : WordLangInst (BitVec width)))
    (_bound : maxVarInstHOL (.fp (.fpFromInt destination input) : WordLangInst (BitVec width)) < 2*frame+2*k)
    (_convention : instArgConventionExact (.fp (.fpFromInt destination input) : HolInst width))
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative (.fp (.fpFromInt destination input)) (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  have reads : ∀ n, StackSemStateOps.getFpVar n target = WordSemStateFiniteExact.getFpVar n source :=
    fun n => (StateRelFp.stateRelGetFpVar ac k f frame source target lens 0 n related).symm
  simp only [WordSemStateFiniteExact.inst] at executed
  repeat' (first | contradiction | split at executed)
  all_goals simp only [Option.some.injEq] at executed
  all_goals subst sourcePost
  all_goals refine ⟨_, ?_, StateRelFp.stateRelSetFpVar ac k f frame source target lens 0 _ _ related, rfl, rfl⟩
  all_goals simp_all [wInstNative,StackSemEvaluate.evaluate_inst,StackSemInst.instHOL,
    StackSemFpInstructions.instFp,StackSemFpRegisterInstructions.instFpRegister,
    StackSemFpRegisterInstructions.instFpFromInt]

end Flapjack.WordToStackProofs.InstSimulation.FpConversions
