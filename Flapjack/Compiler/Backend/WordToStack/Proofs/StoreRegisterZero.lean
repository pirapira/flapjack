import Flapjack.Compiler.Backend.WordToStack.Proofs.StoreRegister
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors

namespace Flapjack.WordToStackProofs.StoreRegisterZero
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

/-- Full original local paired zero-register update law (4629–4654).
The r=0 alias and nonzero register/spill cases retain the original update order.
All native runs, full post-state relation and resource equalities are derived
under exactly the original six guards, for arbitrary word-or-label values.
The evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); this theorem
claims no independent real-analysis agreement. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackStore_wReg1_0"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWStackStoreWReg1Zero {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register physical k f frame : Nat)
    (loads : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (value zeroValue : WordLocW width) (stackLength stackSpace : Nat)
    (compiled : wReg1 register (k,f,frame) = (loads,physical))
    (even : register % 2 = 0) (bound : register < 2*frame+2*k)
    (related : stateRel ac k f frame source target lens 0)
    (lengthEq : target.stack.length = stackLength) (spaceEq : target.stackSpace = stackSpace) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackStoreNative loads .skip,
        StackSemStateOps.setVar 0 zeroValue (StackSemStateOps.setVar physical value target)) =
          (none,post) ∧
      stateRel ac k f frame
        (WordSemStateFiniteExact.setVar 0 zeroValue
          (WordSemStateFiniteExact.setVar register value source)) post lens 0 ∧
      post.stack.length = stackLength ∧ post.stackSpace = stackSpace := by
  have large : 4 < k := by unfold stateRel at related; tauto
  have positive : 0 < k := by omega
  by_cases zero : register = 0
  · subst register
    have physicalZero : physical = 0 := by
      simpa [wReg1, positive] using (congrArg Prod.snd compiled).symm
    subst physical
    simpa only [NativeStackAccessors.setVarCancel, NativeWordAccessors.setVarCancelWord] using
      StoreRegister.evaluateWStackStoreWReg1 ac 0 0 k f frame loads source target lens
        zeroValue stackLength stackSpace compiled even bound related lengthEq spaceEq
  · have physicalNe : physical ≠ 0 := by
      by_cases inReg : register / 2 < k
      · have physicalEq : physical = register / 2 := by
          simpa [wReg1, inReg] using (congrArg Prod.snd compiled).symm
        omega
      · have physicalEq : physical = k := by
          simpa [wReg1, inReg] using (congrArg Prod.snd compiled).symm
        omega
    rw [NativeStackAccessors.setVarSwap 0 physical zeroValue value target (Ne.symm physicalNe),
      NativeWordAccessors.setVarSwapWord 0 register zeroValue value source (Ne.symm zero)]
    have relatedZero : stateRel ac k f frame
        (WordSemStateFiniteExact.setVar 0 zeroValue source)
        (StackSemStateOps.setVar 0 zeroValue target) lens 0 := by
      simpa using StateRelRegisterUpdate.stateRelSetVar 0 zeroValue related positive
    exact StoreRegister.evaluateWStackStoreWReg1 ac register physical k f frame loads
      (WordSemStateFiniteExact.setVar 0 zeroValue source)
      (StackSemStateOps.setVar 0 zeroValue target) lens value stackLength stackSpace
      compiled even bound relatedZero lengthEq spaceEq

end Flapjack.WordToStackProofs.StoreRegisterZero
