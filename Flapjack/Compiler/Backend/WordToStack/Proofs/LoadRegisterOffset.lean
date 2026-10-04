import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegister

namespace Flapjack.WordToStackProofs.LoadRegisterOffset
open Flapjack.Compiler.Encoders.Asm
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

/-- Flapjack factoring of original source offset-expression success: its
actual input is a word and its actual wordOpHOL calculation gives the result.
No target read or desired expression equality is assumed. -/
private theorem sourceOffsetRead {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (r : Nat) (constant result : BitVec width)
    (expression : WordSemStateFiniteExact.wordExp source (.op .add [.var r,.const constant]) =
      some (.word result)) :
    ∃ value : BitVec width, WordSemStateFiniteExact.getVar r source = some (.word value) ∧
      wordOpHOL .add [value,constant] = some result := by
  cases read : WordSemStateFiniteExact.getVar r source with
  | none => simp [WordSemStateFiniteExact.wordExp,theWords,read] at expression
  | some input =>
    cases input with
    | loc l n => simp [WordSemStateFiniteExact.wordExp,theWords,read] at expression
    | word value =>
      cases calculation : wordOpHOL .add [value,constant] with
      | none => simp [WordSemStateFiniteExact.wordExp,theWords,read,calculation] at expression
      | some output =>
        simp [WordSemStateFiniteExact.wordExp,theWords,read,calculation] at expression
        subst output
        exact ⟨value,rfl,calculation⟩

/-- Full original local evaluate_wStackLoad_wReg1_with_const4447–4469.
All four guards and seven-conjunct conclusion are retained, with arbitrary
word constant/result, physical or spill source and full source/target carriers.
The actual source word read and calculation derive the actual native load and
target expression success; no target-run or target-expression premise is used.
The evaluators inherit reals_as_rational_cuts (SOUNDNESS item 8), without
an independent agreement claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_wReg1_with_const"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWStackLoadWReg1WithConst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame r reg : Nat) (loads : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (constant result : BitVec width)
    (guards : wReg1 r (k,f,frame) = (loads,reg) ∧ r % 2 = 0 ∧
      WordSemStateFiniteExact.wordExp source (.op .add [.var r,.const constant]) = some (.word result) ∧
      stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackLoadNative loads .skip,target) = (none,post) ∧
      target.clock = post.clock ∧ stateRel ac k f frame source post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace ∧
      reg ≠ k+1 ∧ StackSemExpressions.wordExp post (.op .add [.var reg,.const constant]) = some result := by
  obtain ⟨compiled,even,expression,related⟩ := guards
  obtain ⟨value,read,calculation⟩ := sourceOffsetRead source r constant result expression
  obtain ⟨post,run,clock,postRel,length,space,_,_,notScratch,physicalRead⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r reg loads source target lens
      (.word value) compiled even read related
  refine ⟨post,run,clock,postRel,length,space,notScratch,?_⟩
  have lookup : post.regs.lookup reg = some (.word value) := physicalRead
  simp [StackSemExpressions.wordExp,lookup,calculation]

end Flapjack.WordToStackProofs.LoadRegisterOffset
