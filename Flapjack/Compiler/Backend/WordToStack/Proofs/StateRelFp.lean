import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

namespace Flapjack.WordToStackProofs.StateRelFp
open Flapjack.Compiler.Encoders.Asm

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

/-- Full original FP read law4402–4407: the whole relation implies equality
of actual FP reads at every index, including absent entries. Fixed word64 FP
payloads and arbitrary positive machine width are retained. Structural equality
establishes no numerical FP agreement and uses no real-arithmetic assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_get_fp_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelGetFpVar {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra n : Nat)
    (related : stateRel ac k f frame source target lens extra) :
    WordSemStateFiniteExact.getFpVar n source = StackSemStateOps.getFpVar n target := by
  have sameFp : target.fpRegs = source.fpRegs :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [WordSemStateFiniteExact.getFpVar,StackSemStateOps.getFpVar,sameFp]

/-- Full original FP update law4409–4415: simultaneous actual updates with
an arbitrary word64 value preserve the entire original relation for arbitrary
extra and index. No postrelation premise or numerical FP agreement is assumed;
no real-arithmetic assumption is used. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_fp_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetFpVar {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra n : Nat)
    (value : BitVec 64)
    (related : stateRel ac k f frame source target lens extra) :
    stateRel ac k f frame (WordSemStateFiniteExact.setFpVar n value source)
      (StackSemStateOps.setFpVar n value target) lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩ := related
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,
    congrArg (fun m => m.updateEq (n,value)) h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩

end Flapjack.WordToStackProofs.StateRelFp
