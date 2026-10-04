import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Simple
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

/-!
# `word_cseProof` `comp_correct`: the control-flow cases

The `MustTerminate`, `Seq`, `If` and `Loop` cases of HOL `comp_correct`
(`word_cseProof:3630-3697, 3765-3791`). Each piece has HOL's statement at the
constructor plus exactly the induction hypotheses `evaluate_ind` provides for
it.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace CompCorrectControlCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompCorrectControlCarrier

/-- HOL `comp_correct`, `MustTerminate` case (`word_cseProof:3630-3645`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_MustTerminate {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ih : s.termdep ≠ 0 →
      CompCorrectAt p { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }) :
    CompCorrectAt (.mustTerminate p) s := by
  rintro res s' data p' data' ⟨he, hf, hd, hres, hw⟩
  simp only [flatExpConventions] at hf
  rcases hc : wordCse data p with ⟨d1, q1⟩
  simp only [wordCse, hc] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  rw [evaluate] at he
  split at he
  · cases he; exact absurd rfl hres
  · rename_i htd
    set sm : WordSemStateFiniteExact width C F :=
      { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } with hsm
    rcases he1 : evaluate p sm with ⟨r1, s1⟩
    rw [he1] at he
    simp only at he
    split at he
    · cases he; exact absurd rfl hres
    · rename_i hto
      cases he
      have hd1 := data_inv_clock data s (wordSemMustTerminateLimit width) (s.termdep - 1) hd
      obtain ⟨e1, i1⟩ := ih htd res s1 data q1 d1 ⟨he1, hf, hd1, hres, hc⟩
      refine ⟨?_, fun hn => data_inv_clock d1 s1 s.clock s.termdep (i1 hn)⟩
      rw [evaluate, dif_neg htd, e1]
      simp only

/-- HOL `comp_correct`, `Seq` case (`word_cseProof:3647-3662`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Seq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (ih : (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → CompCorrectAt c2 s1) ∧
      CompCorrectAt c1 s) :
    CompCorrectAt (.seq c1 c2) s := by
  rintro res s' data p' data' ⟨he, hf, hd, hres, hw⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hf
  rcases hc1 : wordCse data c1 with ⟨d1, q1⟩
  rcases hc2 : wordCse d1 c2 with ⟨d2, q2⟩
  simp only [wordCse, hc1, hc2] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  rcases he1 : evaluate c1 s with ⟨r1, s1⟩
  rw [evaluate, fix_clock_evaluate, he1] at he
  cases r1 with
  | none =>
    simp only at he
    obtain ⟨e1, i1⟩ := ih.2 none s1 data q1 d1 ⟨he1, hf.1, hd, by simp, hc1⟩
    obtain ⟨e2, i2⟩ := ih.1 none s1 ⟨he1.symm, rfl⟩ res s' d1 q2 d2 ⟨he, hf.2, i1 rfl, hres, hc2⟩
    exact ⟨by rw [evaluate, fix_clock_evaluate, e1]; exact e2, i2⟩
  | some x =>
    simp only at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨e1, -⟩ := ih.2 (some x) s1 data q1 d1 ⟨he1, hf.1, hd, hres, hc1⟩
    exact ⟨by rw [evaluate, fix_clock_evaluate, e1], fun h => by cases h⟩

/-- HOL `comp_correct`, `If` case (`word_cseProof:3676-3697`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_If {width : Nat} [NeZero width] {C : Type} {F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (ih : (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ v = true → CompCorrectAt c1 s) ∧
      (∀ v3 v4 x y v, (getVar r1 s, WordSemStateFiniteExact.getVarImm ri s) = (v3, v4) ∧ v3 = some x ∧ v4 = some y ∧
        wordSemWordCmp cmp x y = some v ∧ ¬ v = true → CompCorrectAt c2 s)) :
    CompCorrectAt (.ite cmp r1 ri c1 c2) s := by
  rintro res s' data p' data' ⟨he, hf, hd, hres, hw⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hf
  rcases hc1 : wordCse data c1 with ⟨d1, q1⟩
  rcases hc2 : wordCse data c2 with ⟨d2, q2⟩
  simp only [wordCse, hc1, hc2] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  have wf1 : wfData width d1 := by
    have := word_cse_wf_data c1 data hd.1; rw [hc1] at this; exact this
  have wf2 : wfData width d2 := by
    have := word_cse_wf_data c2 data hd.1; rw [hc2] at this; exact this
  rw [evaluate] at he
  split at he
  · rename_i x y hx hy
    split at he
    · rename_i hcmp
      obtain ⟨e1, i1⟩ := ih.1 _ _ x y true ⟨rfl, hx, hy, hcmp, rfl⟩ res s' data q1 d1
        ⟨he, hf.1, hd, hres, hc1⟩
      refine ⟨by rw [evaluate, hx, hy]; simp only [hcmp]; exact e1, fun hn => ?_⟩
      exact data_inv_merge_l d1 d2 s' ⟨wf1, wf2, (i1 hn).2⟩
    · rename_i hcmp
      obtain ⟨e2, i2⟩ := ih.2 _ _ x y false ⟨rfl, hx, hy, hcmp, by simp⟩ res s' data q2 d2
        ⟨he, hf.2, hd, hres, hc2⟩
      refine ⟨by rw [evaluate, hx, hy]; simp only [hcmp]; exact e2, fun hn => ?_⟩
      exact data_inv_merge_r d1 d2 s' ⟨wf1, wf2, (i2 hn).2⟩
    · cases he; exact absurd rfl hres
  · cases he; exact absurd rfl hres

/-- HOL `comp_correct`, `Loop` case (`word_cseProof:3765-3791`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Loop {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width)) (exitNames : WordLangNumSetHOL)
    (s : WordSemStateFiniteExact width C F)
    (ih : (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
        wordSemContLoop res = true ∧ s1.clock ≠ 0 →
        CompCorrectAt (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
      (∀ v, cutState (names, .ln) s = some v → CompCorrectAt c v)) :
    CompCorrectAt (.loop names c exitNames) s := by
  rintro res s' data p' data' ⟨he, hf, hd, hres, hw⟩
  simp only [flatExpConventions] at hf
  rcases hc : wordCse emptyData c with ⟨d0, c'⟩
  simp only [wordCse, hc] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨?_, fun _ => dataInvEmpty s'⟩
  rw [evaluate] at he
  split at he
  · cases he; exact absurd rfl hres
  · rename_i v hv
    rw [fix_clock_evaluate] at he
    rcases he1 : evaluate c v with ⟨q, r⟩
    rw [he1] at he
    simp only at he
    have hq : q ≠ some .error := by
      rintro rfl
      simp only [wordSemContLoop, Bool.false_eq_true, if_false] at he
      cases he; exact hres rfl
    obtain ⟨e1, -⟩ := ih.2 v hv q r emptyData c' d0 ⟨he1, hf, dataInvEmpty v, hq, hc⟩
    rw [evaluate]
    split
    · rename_i hv'; rw [hv] at hv'; cases hv'
    · rename_i v' hv'
      rw [hv] at hv'; cases hv'
      rw [fix_clock_evaluate, e1]
      simp only
      split
      · rename_i hcont
        rw [if_pos hcont] at he
        split
        · rename_i hclk; rw [dif_pos hclk] at he; exact he
        · rename_i hclk
          rw [dif_neg hclk] at he
          obtain ⟨e2, -⟩ := ih.1 v q r ⟨hv, he1.symm, hcont, hclk⟩ res s' emptyData
            (.loop names c' exitNames) emptyData
            ⟨he, by simpa [wordSemSTOP, flatExpConventions] using hf, dataInvEmpty _, hres,
              by simp [wordSemSTOP, wordCse, hc]⟩
          exact e2
      · rename_i hcont
        rw [if_neg hcont] at he
        exact he

end Flapjack.Compiler.Backend.WordCse
