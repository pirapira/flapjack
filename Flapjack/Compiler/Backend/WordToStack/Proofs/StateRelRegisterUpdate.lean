import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Misc.Sptree.Wf
namespace Flapjack.WordToStackProofs.StateRelRegisterUpdate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
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



/-- Full original physical-register update law (2930–2951). Every stateRel
conjunct, arbitrary extra offset and Word/Loc payload is retained. The inherited
real carrier is unchanged; this structural update asserts no FP equivalence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetVar {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (x : Nat) (value : WordLocW width)
    (related : stateRel ac k f frame source target lens extra) (physical : x < k) :
    stateRel ac k f frame (WordSemStateFiniteExact.setVar (2*x) value source)
      (StackSemStateOps.setVar x value target) lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,?_,
    h37,h38,?_⟩
  · exact sptWfInsert (2*x) value source.locals h36
  · intro n v found
    change sptLookup n (sptInsert (2*x) value source.locals) = some v at found
    by_cases same : n = 2*x
    · subst n
      rw [sptLookup_sptInsert_same] at found
      have valueEq : value = v := Option.some.inj found
      subst v
      have half : 2*x/2 = x := by omega
      simp [half, physical, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL]
    · rw [sptLookup_sptInsert_ne (2*x) n value source.locals same] at found
      obtain ⟨even, placement⟩ := hloc n v found
      refine ⟨even, ?_⟩
      by_cases inReg : n/2 < k
      · rw [if_pos inReg] at placement ⊢
        have different : n/2 ≠ x := by omega
        simpa [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL,
          different] using placement
      · rw [if_neg inReg] at placement ⊢
        exact placement
/-- Full original spilled-local update law (2962–2997), including the explicit
original stack/space equalities and every full stateRel conjunct. Bounds follow
from the original relation and source index guards. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var2"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]

theorem wordToStackStateRelSetVar2 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat}
    (x : Nat) (value : WordLocW width) (st : List (WordLocW width)) (sp : Nat)
    (related : stateRel ac k f frame source target lens 0)
    (spilled : ¬x < k) (bound : x < frame+k)
    (stackEq : st = target.stack) (spaceEq : sp = target.stackSpace) :
    stateRel ac k f frame (WordSemStateFiniteExact.setVar (2*x) value source)
      {target with stack := st.set (sp+(f+k-(x+1))) value} lens 0 := by
  subst st; subst sp
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  have frameShape : f = frame+1 := by split at h35 <;> omega
  have framePositive : 0 < f := by omega
  have slotBound : f+k-(x+1) < f := by omega
  have slotLength : target.stackSpace+(f+k-(x+1)) < target.stack.length := by omega
  have restEq :
      ((target.stack.set (target.stackSpace+(f+k-(x+1))) value).drop
        (target.stackSpace+0)).drop f = (target.stack.drop (target.stackSpace+0)).drop f := by
    rw [List.drop_drop, List.drop_drop]
    exact List.drop_set_of_lt (by omega)
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,?_,?_,h35,?_,?_,?_,?_⟩
  · simpa using h33
  · simpa using h34
  · exact sptWfInsert (2*x) value source.locals h36
  · simpa [stackSizeRel, WordSemStateFiniteExact.setVar] using h37
  · simpa only [WordSemStateFiniteExact.setVar, restEq, List.length_set] using h38
  · intro n v found
    change sptLookup n (sptInsert (2*x) value source.locals) = some v at found
    by_cases same : n = 2*x
    · subst n
      rw [sptLookup_sptInsert_same] at found
      have valueEq : value = v := Option.some.inj found
      subst v
      have half : 2*x/2 = x := by omega
      have indexEq : f-1-(x-k) = f+k-(x+1) := by omega
      refine ⟨by omega, ?_⟩
      simp only [half, Nat.add_zero, if_neg spilled]
      refine ⟨?_, by omega⟩
      rw [List.getElem?_take, List.getElem?_drop]
      simp [indexEq,slotBound,slotLength]
    · rw [sptLookup_sptInsert_ne (2*x) n value source.locals same] at found
      obtain ⟨even, placement⟩ := hloc n v found
      refine ⟨even, ?_⟩
      by_cases inReg : n/2 < k
      · simpa only [if_pos inReg] using placement
      · rw [if_neg inReg] at placement ⊢
        refine ⟨?_,placement.2⟩
        have different : target.stackSpace+(f+k-(x+1)) ≠
            target.stackSpace+(f-1-(n/2-k)) := by omega
        simpa only [Nat.add_zero,List.getElem?_take,List.getElem?_drop,
          List.length_set,List.getElem?_set_ne different] using placement.1

/-- Writing a target register `n` that no source variable maps to (`k ≤ n`)
leaves the relation unchanged. Flapjack factoring of both conjuncts of
`state_rel_set_var_k`; no separate HOL declaration. -/
theorem stateRelSetVarHigh {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (n : Nat) (value : WordLocW width) (high : k ≤ n) :
    stateRel ac k f frame source (StackSemStateOps.setVar n value target) lens extra ↔
      stateRel ac k f frame source target lens extra := by
  unfold stateRel
  have regs : ∀ m, m < k → (StackSemStateOps.setVar n value target).regs.lookup m =
      target.regs.lookup m := by
    intro m hm
    have : m ≠ n := by omega
    simp [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, this]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,hloc⟩
    refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,fun m v found => ?_⟩
    obtain ⟨even, placement⟩ := hloc m v found
    refine ⟨even, ?_⟩
    split at placement
    · rename_i inReg
      rw [if_pos inReg, ← regs _ inReg]
      exact placement
    · rename_i inReg
      rw [if_neg inReg]
      exact placement
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,hloc⟩
    refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,fun m v found => ?_⟩
    obtain ⟨even, placement⟩ := hloc m v found
    refine ⟨even, ?_⟩
    split at placement
    · rename_i inReg
      rw [if_pos inReg, regs _ inReg]
      exact placement
    · rename_i inReg
      rw [if_neg inReg]
      exact placement

/-- Full original `state_rel_set_var_k` (2917–2928): writing target register
`k+1` or `k` (the two scratch registers) leaves the relation unchanged, for every
extra offset. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var_k"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetVarK {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    {value : WordLocW width} :
    (stateRel ac k f frame source (StackSemStateOps.setVar (k+1) value target) lens extra ↔
      stateRel ac k f frame source target lens extra) ∧
    (stateRel ac k f frame source (StackSemStateOps.setVar k value target) lens extra ↔
      stateRel ac k f frame source target lens extra) :=
  ⟨stateRelSetVarHigh (k+1) value (by omega), stateRelSetVarHigh k value (Nat.le_refl k)⟩

end Flapjack.WordToStackProofs.StateRelRegisterUpdate
