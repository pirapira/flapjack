import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

namespace Flapjack.WordToStackProofs.StateRelMemory
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

/-- Full original state_rel_with_memory4387: arbitrary simultaneous total
memory replacement preserves every stateRel conjunct for arbitrary extra.
The original implication is the only premise; no post-state relation is
assumed. All unrelated fields and compiler/stack obligations are preserved. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_with_memory"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelWithMemory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat)
    (memory : BitVec width → WordLocW width)
    (related : stateRel ac k f frame source target lens extra) :
    stateRel ac k f frame {source with memory := memory} {target with memory := memory} lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩ := related
  exact ⟨h1,h2,h3,h4,h5,h6,h7,rfl,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩

/-- Full original state_rel_mem_store3836: actual source memStore success
and the full original relation derive the actual target memStore success and
entire post-state relation. Arbitrary address, Word/Loc payload and extra are
retained. Domain membership and the target memory update are derived internally. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_mem_store"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelMemStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat)
    (address : BitVec width) (value : WordLocW width)
    (guards : stateRel ac k f frame source target lens extra ∧
      WordSemStateFiniteExact.memStore address value source = some sourcePost) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemStateOps.memStore address value target = some post ∧
      stateRel ac k f frame sourcePost post lens extra := by
  obtain ⟨related,executed⟩ := guards
  have sameMemory : target.memory = source.memory := related.2.2.2.2.2.2.2.1
  have sameDomain : target.mdomain = source.mdomain := related.2.2.2.2.2.2.2.2.1
  simp only [WordSemStateFiniteExact.memStore] at executed
  split at executed
  next inDomain =>
    cases executed
    refine ⟨{target with memory := fun key => if key = address then value else source.memory key},?_,?_⟩
    · simp only [StackSemStateOps.memStore,sameDomain,inDomain,if_true,sameMemory]
    · exact stateRelWithMemory ac k f frame source target lens extra _ related
  next => contradiction

end Flapjack.WordToStackProofs.StateRelMemory
