import Flapjack.Compiler.Backend.WordCse.Proofs.MoveLemmas

/-!
# `word_cseProof` `comp_correct`: the non-recursive simple cases

The cases of HOL `comp_correct` (`word_cseProof:3305-3793`) whose programs do
not recurse and whose CSE step is a reset, the identity, a move, a register
write through a fact producer, or a state update that leaves the invariant's
reads unchanged. Each piece states HOL's `comp_correct` at that program
constructor; `CompCorrectAt` is exactly HOL's quantified statement body.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace CompCorrectSimpleCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompCorrectSimpleCarrier

/-- HOL `comp_correct`'s statement at program `p` and state `s`
    (`word_cseProof:3306-3309`): for every result, final state and knowledge,
    a non-error, flat run from an invariant-satisfying state is reproduced by
    the transformed program, and a normal result re-establishes the invariant
    for the output knowledge. Flapjack abbreviation of the HOL quantified body. -/
def CompCorrectAt {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F)
    (data : Knowledge) (p' : WordLangProgHOL (BitVec width)) (data' : Knowledge),
    evaluate p s = (res, s') ∧ flatExpConventions p = true ∧ dataInv data s ∧
      res ≠ some .error ∧ wordCse data p = (data', p') →
    evaluate p' s = (res, s') ∧ (res = none → dataInv data' s')

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem data_inv_invalidate (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat)
    (h : dataInv data s) : dataInv (invalidateData data r) s :=
  data_inv_invalidate_regs [r] data s h

/-- A CSE step that resets the knowledge and keeps the program (Flapjack
    infrastructure). -/
theorem compCorrectAt_reset (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hc : ∀ data, wordCse data p = (emptyData, p)) : CompCorrectAt p s := by
  rintro res s' data p' data' ⟨he, -, -, -, hw⟩
  rw [hc data] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  exact ⟨he, fun _ => dataInvEmpty s'⟩

/-- A CSE step that keeps both knowledge and program, for a program with no
    normal result (Flapjack infrastructure). -/
theorem compCorrectAt_abnormal (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (hc : ∀ data, wordCse data p = (data, p)) (hn : ∀ res s', evaluate p s = (res, s') → res ≠ none) :
    CompCorrectAt p s := by
  rintro res s' data p' data' ⟨he, -, -, -, hw⟩
  rw [hc data] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  exact ⟨he, fun h => absurd h (hn res s' he)⟩

end Helpers

/-- HOL `comp_correct`, `Skip` case (`word_cseProof:3343-3345`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Skip {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) : CompCorrectAt (.skip : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun _ => ?_⟩
  rw [evaluate] at he; cases he; exact hd

/-- HOL `comp_correct`, `Alloc` case (`word_cseProof:3347-3349`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Alloc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.alloc n names : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_reset _ s (fun _ => rfl)

/-- HOL `comp_correct`, `Install` case (`word_cseProof:3708-3710`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Install {width : Nat} [NeZero width] {C : Type} {F : Type}
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.install ptr len dptr dlen names : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_reset _ s (fun _ => rfl)

/-- HOL `comp_correct`, `FFI` case (`word_cseProof:3726-3728`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_FFI {width : Nat} [NeZero width] {C : Type} {F : Type}
    (ffiIndex : Flapjack.Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.ffi ffiIndex ptr1 len1 ptr2 len2 names : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_reset _ s (fun _ => rfl)

/-- HOL `comp_correct`, `Call` case (`word_cseProof:3730-3732`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Call {width : Nat} [NeZero width] {C : Type} {F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.call ret dest args handler) s :=
  compCorrectAt_reset _ s (fun _ => rfl)

/-- HOL `comp_correct`, `Return` case (`word_cseProof:3664-3668`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Return {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (ms : List Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.return n ms : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_abnormal _ s (fun _ => rfl) (fun res s' he => by
    rw [evaluate] at he
    split at he <;> (cases he; simp))

/-- HOL `comp_correct`, `Raise` case (`word_cseProof:3670-3674`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Raise {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.raise n : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_abnormal _ s (fun _ => rfl) (fun res s' he => by
    rw [evaluate] at he
    split at he
    · cases he; simp
    · split at he <;> (cases he; simp))

/-- HOL `comp_correct`, `Break` case (handled by HOL's final `gvs [word_cse_def]`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Break {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.break k : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_abnormal _ s (fun _ => rfl) (fun res s' he => by
    rw [evaluate] at he; cases he; simp)

/-- HOL `comp_correct`, `Continue` case (handled by HOL's final `gvs [word_cse_def]`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Continue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.continue k : WordLangProgHOL (BitVec width)) s :=
  compCorrectAt_abnormal _ s (fun _ => rfl) (fun res s' he => by
    rw [evaluate] at he; cases he; simp)

/-- HOL `comp_correct`, `Store` case (`word_cseProof:3617-3619`): excluded by
    `flat_exp_conventions`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Store {width : Nat} [NeZero width] {C : Type} {F : Type}
    (exp : WordLangExpHOL (BitVec width)) (v : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.store exp v) s := by
  rintro res s' data p' data' ⟨-, hf, -⟩
  simp [flatExpConventions] at hf

/-- HOL `comp_correct`, `Assign` case (`word_cseProof:3486-3488`): excluded by
    `flat_exp_conventions`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Assign {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v : Nat) (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.assign v exp) s := by
  rintro res s' data p' data' ⟨-, hf, -⟩
  simp [flatExpConventions] at hf

/-- HOL `comp_correct`, `Tick` case (`word_cseProof:3621-3628`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Tick {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) : CompCorrectAt (.tick : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  rw [evaluate] at he
  split at he
  · cases he; simp at hn
  · cases he; exact data_inv_clock data s (s.clock - 1) s.termdep hd

/-- HOL `comp_correct`, `CodeBufferWrite` case (`word_cseProof:3712-3717`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_CodeBufferWrite {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.codeBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  rw [evaluate] at he
  split at he
  · split at he
    · cases he; exact data_inv_state_agree data s _ ⟨hd, rfl, rfl, rfl, rfl, rfl⟩
    · cases he; simp at hn
  · cases he; simp at hn

/-- HOL `comp_correct`, `DataBufferWrite` case (`word_cseProof:3719-3724`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_DataBufferWrite {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.dataBufferWrite r1 r2 : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  rw [evaluate] at he
  split at he
  · split at he
    · cases he; exact data_inv_state_agree data s _ ⟨hd, rfl, rfl, rfl, rfl, rfl⟩
    · cases he; simp at hn
  · cases he; simp at hn

/-- HOL `comp_correct`, `Move` case (`word_cseProof:3351-3355`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Move {width : Nat} [NeZero width] {C : Type} {F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.move pri moves : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  rw [evaluate] at he
  split at he
  · rename_i hnd
    split at he
    · cases he; simp at hn
    · rename_i vs hg
      cases he
      exact canonicalMoveRegs_lemma data s moves vs ⟨hd, hnd, hg⟩
  · cases he; simp at hn

/-- HOL `comp_correct`, `LocValue` case (`word_cseProof:3699-3706`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_LocValue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r l : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.locValue r l : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, hres, hw⟩
  simp only [wordCse] at hw
  rw [evaluate] at he
  split at he
  · rename_i hmem
    cases he
    obtain ⟨h1, h2⟩ := add_to_data_LocValue_correct (invalidateData data r) s r l data' p'
      ⟨data_inv_invalidate data s r hd, lookup_invalidateData_self data r, hmem, hw⟩
    exact ⟨h1, fun _ => h2⟩
  · cases he; exact absurd rfl hres

/-- HOL `comp_correct`, `OpCurrHeap` case (`word_cseProof:3602-3615`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_OpCurrHeap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (b : BinOp) (dst src : Nat) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.opCurrHeap b dst src : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, hres, hw⟩
  simp only [wordCse] at hw
  have dD := data_inv_invalidate data s dst hd
  have rD := lookup_invalidateData_self data dst
  rw [evaluate] at he
  split at he
  · cases he; exact absurd rfl hres
  · rename_i w hexp
    cases he
    split at hw
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
      exact ⟨by rw [evaluate, hexp], fun _ => (data_inv_set_var _ s dst w rD).mpr dD⟩
    · rename_i hguard
      simp only [not_or] at hguard
      obtain ⟨h1, h2⟩ := add_to_data_OpCurrHeap_correct _ s b dst src _ w data' p'
        ⟨dD, rD, rfl, hguard.1, hguard.2, hexp, hw⟩
      exact ⟨h1, fun _ => h2⟩

/-- HOL `comp_correct`, `StoreConsts` case (`word_cseProof:3734-3740`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_StoreConsts {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t1 t2 addr offset : Nat) (words : List (Bool × BitVec width)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.storeConsts t1 t2 addr offset words) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  set d := invalidateRegs data [t1, t2, addr, offset]
  have dd : dataInv d s := data_inv_invalidate_regs _ data s hd
  have un : ∀ x ∈ [t1, t2, addr, offset],
      sptLookup x ({ d with loadsMem := Misc.BalancedMap.empty } : Knowledge).toCanonical = none :=
    fun x hx => lookup_invalidate_regs _ data x hx
  rw [evaluate] at he
  split at he
  · split at he
    · cases he; simp at hn
    · cases he
      refine (data_inv_set_var _ _ addr _ (un addr (by simp))).mpr ?_
      refine (data_inv_set_var _ _ offset _ (un offset (by simp))).mpr ?_
      refine (data_inv_unset_var _ _ t1 (un t1 (by simp))).mpr ?_
      refine (data_inv_unset_var _ _ t2 (un t2 (by simp))).mpr ?_
      exact data_inv_memory d s _ dd
  · cases he; simp at hn

end Flapjack.Compiler.Backend.WordCse
