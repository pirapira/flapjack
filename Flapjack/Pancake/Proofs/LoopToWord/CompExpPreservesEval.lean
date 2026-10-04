import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.GoodDimindex

/-!
# `loop_to_wordProof` `comp_exp_preserves_eval`

Counterpart of `cakeml/pancake/proofs/loop_to_wordProofScript.sml:461-509`
(bead `flapjack-pxn.18.5.9.18.3`).  This is the expression-level simulation
of `loop_to_word`: a loopLang expression that evaluates to `v` compiles, via
`comp_exp`, to a wordLang expression that `word_exp` evaluates to the same
`v`.  It is stated over these tagged exact ports:
* the loopSem `eval` and the wordSem `word_exp`;
* `comp_exp` (`compExpHOL`);
* `state_rel` and `locals_rel`.
-/

namespace Flapjack

namespace LoopToWordCompExpPreservesEvalWitnesses

/-- Same-module roundtrip for the relation qualifier's loopSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's wordSem state fields. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordCompExpPreservesEvalWitnesses

namespace LoopToWord

private theorem attachMap_eq {α β : Type} (l : List α) (f : α → β) :
    (l.attach.map fun (x : { x // x ∈ l }) => f x.1) = l.map f := by
  simp

private theorem theWords_map_of {width : Nat} [NeZero width] {α : Type}
    (f g : α → Option (WordLocW width)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ v, f a = some v → g a = some v) →
      ∀ ws, theWords (l.map f) = some ws → theWords (l.map g) = some ws
  | [], _, ws, h => by simpa [theWords] using h
  | a :: l, hfg, ws, h => by
      simp only [List.map_cons, theWords] at h ⊢
      split at h
      · rename_i x xs hx hxs
        rw [hfg a (List.mem_cons_self ..) _ hx,
          theWords_map_of f g l (fun b hb => hfg b (List.mem_cons_of_mem _ hb)) xs hxs]
        exact h
      · cases h

/-- Recursive core of `comp_exp_preserves_eval`, by recursion on the
    expression as in HOL's `eval_ind`. -/
private theorem compExpPreservesEvalAux {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (hgd : goodDimindex width) (hState : loopToWordStateRelHOLExact s t)
    (hLocals : localsRelHOL ctxt s.locals t.locals) :
    ∀ (e : HolLoopExp width) (v : WordLocW width),
      LoopSemStateFiniteExact.eval s e = some v →
        WordSemStateFiniteExact.wordExp t (compExpHOL ctxt e) = some v
  | .const w, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]; exact h
  | .var n, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      exact localsRelHOLGetVar ctxt s.locals t n v ⟨hLocals, h⟩
  | .lookup name, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hglob, _⟩ := hState
      exact hglob name v h
  | .baseAddr, v, h => by
      simp only [LoopSemStateFiniteExact.eval, Option.some.injEq] at h
      subst h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      obtain ⟨_, _, _, _, _, _, _, hcur, _⟩ := hState
      exact hcur
  | .topAddr, v, h => by
      simp only [LoopSemStateFiniteExact.eval, Option.some.injEq] at h
      subst h
      obtain ⟨len, _, _, _, _, _, _, hcur, hlen, htop, _⟩ := hState
      have hw : 1 < width := by rcases hgd with h | h <;> omega
      rw [compExpHOL]
      simp only [WordSemStateFiniteExact.wordExp, List.attach_cons, List.attach_nil,
        List.map_cons, List.map_nil, WordSemStateFiniteExact.getStore, hcur, hlen]
      have h1 : (1#width).toNat = 1 := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      have hs : wordShiftHOL Shift.lsl len 1 =
          some (len <<< (1 : Nat)) := by
        simp only [wordShiftHOL]; rw [if_neg (by omega)]
      rw [h1, hs]
      simp only [theWords, Option.map_some, wordOpHOL, wordOp, List.foldr_cons, List.foldr_nil,
        htop, Option.some.injEq, WordLocW.word.injEq]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq, Nat.mul_comm]
  | .load address, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      split at h
      · rename_i w hw
        rw [compExpPreservesEvalAux s t ctxt hgd hState hLocals address _ hw]
        obtain ⟨_, hmem, hmd, _⟩ := hState
        simpa [WordSemStateFiniteExact.memLoad, LoopSemStateFiniteExact.memLoad, hmem, hmd]
          using h
      · cases h
  | .shift sh e1 e2, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      split at h
      · rename_i w1 w2 h1 h2
        rw [compExpPreservesEvalAux s t ctxt hgd hState hLocals e1 _ h1,
          compExpPreservesEvalAux s t ctxt hgd hState hLocals e2 _ h2]
        exact h
      · cases h
  | .op operator args, v, h => by
      simp only [LoopSemStateFiniteExact.eval] at h
      rw [compExpHOL, WordSemStateFiniteExact.wordExp]
      have hattach := attachMap_eq args (LoopSemStateFiniteExact.eval s)
      have hattach' := attachMap_eq (args.map (compExpHOL ctxt))
        (WordSemStateFiniteExact.wordExp t)
      rw [hattach] at h
      rw [hattach', List.map_map]
      split at h
      · rename_i ws hws
        rw [theWords_map_of (LoopSemStateFiniteExact.eval s)
          (WordSemStateFiniteExact.wordExp t ∘ compExpHOL ctxt) args
          (fun a ha w hw => by
            have := List.sizeOf_lt_of_mem ha
            exact compExpPreservesEvalAux s t ctxt hgd hState hLocals a w hw) ws hws]
        exact h
      · cases h
  termination_by e => sizeOf e

/-- Exact HOL `comp_exp_preserves_eval` (`loop_to_wordProofScript.sml:461-509`):

    ```
    ∀s (e:'a loopLang$exp) v t ctxt.
      eval s e = SOME v ∧ good_dimindex(:'a) ∧
      state_rel s t /\ locals_rel ctxt s.locals t.locals ==>
      word_exp t (comp_exp ctxt e) = SOME v
    ```

    The target state `t` is typed at the source FFI host `F`, as `state_rel`
    requires, with an arbitrary compiler-configuration type `C`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.fpRegs,
      WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s : LoopSemStateFiniteExact width F) (e : HolLoopExp width) (v : WordLocW width)
      (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat),
      LoopSemStateFiniteExact.eval s e = some v ∧ goodDimindex width ∧
        loopToWordStateRelHOLExact s t ∧ localsRelHOL ctxt s.locals t.locals →
      WordSemStateFiniteExact.wordExp t (compExpHOL ctxt e) = some v := by
  rintro s e v t ctxt ⟨h, hgd, hState, hLocals⟩
  exact compExpPreservesEvalAux s t ctxt hgd hState hLocals e v h

end LoopToWord

end Flapjack
