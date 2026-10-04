import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Simple
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Inst
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Store
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `word_cseProof` `comp_correct`

The assembled HOL `comp_correct` (`word_cseProof:3305-3793`): HOL's
`recInduct evaluate_ind` with its twenty-six cases, each discharged by the
same-tagged case piece of `CompCorrect/`.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace CompCorrectCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompCorrectCarrier

/-- Exact HOL `comp_correct` (`word_cseProof:3305-3793`): a flat, non-error
    run of `v` from a state satisfying `data_inv data` is reproduced by the CSE
    output program, and a normal result re-establishes the invariant for the
    output knowledge. Proved by HOL's `recInduct evaluate_ind`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (v : WordLangProgHOL (BitVec width)) (v1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F)
      (data : Knowledge) (p' : WordLangProgHOL (BitVec width)) (data' : Knowledge),
      evaluate v v1 = (res, s') ∧ flatExpConventions v = true ∧ dataInv data v1 ∧
        res ≠ some .error ∧ wordCse data v = (data', p') →
      evaluate p' v1 = (res, s') ∧ (res = none → dataInv data' s') := by
  intro v v1
  refine evaluate_ind (width := width) (C := C) (F := F) CompCorrectAt
    ⟨comp_correct_Skip, comp_correct_Alloc, comp_correct_StoreConsts, comp_correct_Move,
      comp_correct_Inst, comp_correct_Assign, comp_correct_Get, comp_correct_Set,
      comp_correct_OpCurrHeap, comp_correct_Store, comp_correct_Tick, comp_correct_MustTerminate,
      comp_correct_Seq, comp_correct_Return, comp_correct_Raise, comp_correct_Break,
      comp_correct_Continue, comp_correct_If, comp_correct_Loop, comp_correct_LocValue,
      comp_correct_Install, comp_correct_CodeBufferWrite, comp_correct_DataBufferWrite,
      comp_correct_FFI, comp_correct_ShareInst, fun ret dest args handler s _ =>
        comp_correct_Call ret dest args handler s⟩ v v1

/-- Exact HOL `word_common_subexp_elim_correct` (`word_cseProof:3795-3804`):
    the CSE pass reproduces every flat, non-error run, from `comp_correct` with
    the empty knowledge. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_common_subexp_elim_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_common_subexp_elim_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (h : evaluate p s = (res, s1) ∧ flatExpConventions p = true ∧ res ≠ some .error) :
    evaluate (wordCommonSubexpElim p) s = (res, s1) := by
  obtain ⟨he, hf, hres⟩ := h
  unfold wordCommonSubexpElim
  rcases hc : wordCse emptyData p with ⟨d', p'⟩
  exact (comp_correct p s res s1 emptyData p' d' ⟨he, hf, dataInvEmpty s, hres, hc⟩).1

end Flapjack.Compiler.Backend.WordCse
