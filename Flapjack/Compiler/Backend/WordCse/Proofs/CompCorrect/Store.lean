import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Simple

/-!
# `word_cseProof` `comp_correct`: the store and shared-memory cases

The `Get`, `Set` and `ShareInst` cases of HOL `comp_correct`
(`word_cseProof:3490-3600, 3742-3763`).
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace CompCorrectStoreCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompCorrectStoreCarrier

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- A normal shared-memory instruction changes the FFI state and, for a load,
    its destination register (Flapjack decomposition of the HOL `ShareInst`
    case). -/
theorem shareInst_none (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s s' : WordSemStateFiniteExact width C F) (h : shareInst (rw := width) op v ad s = (none, s')) :
    ∃ f, (isStore op = true ∧ s' = ({ s with ffi := f } : WordSemStateFiniteExact width C F)) ∨
      (isStore op = false ∧ ∃ w, s' = setVar v w ({ s with ffi := f } : WordSemStateFiniteExact width C F)) := by
  cases op <;> simp only [shareInst, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32, shMemStore,
    shMemStoreByte, shMemStore16, shMemStore32] at h <;> (repeat' split at h)
  all_goals first
    | (simp [shMemSetVar] at h; done)
    | (simp at h; done)
    | (obtain ⟨-, rfl⟩ := Prod.mk.inj h; exact ⟨_, Or.inl ⟨rfl, rfl⟩⟩)
    | (simp only [shMemSetVar] at h
       split at h
       all_goals first
         | (simp at h; done)
         | (obtain ⟨-, rfl⟩ := Prod.mk.inj h; exact ⟨_, Or.inr ⟨rfl, _, rfl⟩⟩))

end Helpers

/-- HOL `comp_correct`, `ShareInst` case (`word_cseProof:3742-3763`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_ShareInst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.shareInst op v exp) s := by
  rintro res s' data p' data' ⟨he, -, hd, -, hw⟩
  simp only [wordCse] at hw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨he, fun hn => ?_⟩
  subst hn
  rw [evaluate] at he
  split at he
  · obtain ⟨f, hst | hld⟩ := shareInst_none op v _ s s' he
    · obtain ⟨hst, rfl⟩ := hst
      simp only [hst, if_true]
      exact data_inv_state_agree data s _ ⟨hd, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨hst, w, rfl⟩ := hld
      simp only [hst, Bool.false_eq_true, if_false]
      refine (data_inv_set_var _ _ v w (lookup_invalidateData_self data v)).mpr ?_
      exact data_inv_state_agree _ s _ ⟨data_inv_invalidate data s v hd, rfl, rfl, rfl, rfl, rfl⟩
  · cases he

/-- HOL `comp_correct`, `Get` case (`word_cseProof:3490-3547`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Get {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v : Nat) (name : WordStoreHOL) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.get v name : WordLangProgHOL (BitVec width)) s := by
  rintro res s' data p' data' ⟨he, -, hd, hres, hw⟩
  simp only [wordCse, getClause] at hw
  rw [evaluate] at he
  split at he
  · cases he; exact absurd rfl hres
  · rename_i x hx
    cases he
    have dD := data_inv_invalidate data s v hd
    have rD := lookup_invalidateData_self data v
    have orig : evaluate (.get v name : WordLangProgHOL (BitVec width)) s = (none, setVar v x s) := by
      rw [evaluate, hx]
    split at hw
    · rename_i hn
      split at hw
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨orig, fun _ => (data_inv_set_var _ s v x rD).mpr dD⟩
      · rename_i hev
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        refine ⟨orig, fun _ => data_inv_insert_gets _ (setVar v x s) name v x
          ⟨(data_inv_set_var _ s v x rD).mpr dD, rD, by omega, hn, hx, getVar_setVar_same v x s⟩⟩
    · rename_i k hk
      obtain ⟨w, hsw, hgk⟩ := dD.2.2.2.2.2.2.2.1 name k hk
      have hwx : w = x := by
        have : getStore name s = some w := hsw
        rw [hx] at this; exact (Option.some.inj this).symm
      subst hwx
      have hmove : evaluate (.move 1 [(v, (sptLookup k (invalidateData data v).toLatest).getD k)]) s =
          (none, setVar v w s) :=
        evaluate_Move1 1 v _ w s (by rw [getVar_latest _ s dD.2 k]; exact hgk)
      split at hw
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨hmove, fun _ => (data_inv_set_var _ s v w rD).mpr dD⟩
      · rename_i hev
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨hmove, fun _ => data_inv_repoint _ s v k w dD rD (by omega)
          (dD.1.2.2.2.2.2.1 name k hk) hgk⟩

/-- HOL `comp_correct`, `Set` case (`word_cseProof:3549-3600`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Set {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.set x exp) s := by
  rintro res s' data p' data' ⟨he, -, hd, hres, hw⟩
  simp only [wordCse, setClause] at hw
  rw [evaluate] at he
  split at he
  · cases he; exact absurd rfl hres
  · rename_i hnot
    split at he
    · cases he; exact absurd rfl hres
    · rename_i w hexp
      cases he
      have orig : evaluate (.set x exp) s = (none, setStore x w s) := by
        rw [evaluate, if_neg hnot, hexp]
      have hnf : ∀ (d : Knowledge), (d.getsMem.filter (fun entry => decide (entry.1 ≠ x))).lookup x = none :=
        fun d => List.lookup_eq_none_iff.mpr (fun p hp => by
          have := (List.mem_filter.mp hp).2
          simp only [decide_eq_true_eq] at this
          simpa [bne_iff_ne] using (Ne.symm this))
      split at hw
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨orig, fun _ => dataInvEmpty _⟩
      · rename_i hcur
        have dF := data_inv_filter_gets data s x hd
        have sF := data_inv_set_store _ s x w ⟨dF, hcur, hnf data⟩
        split at hw
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
          exact ⟨orig, fun _ => sF⟩
        · rename_i n hn
          split at hw
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
            exact ⟨orig, fun _ => sF⟩
          · rename_i hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
            refine ⟨orig, fun _ => ?_⟩
            have e : (sptLookup n data.toCanonical).getD n = lookupAny n data.toCanonical n := by
              unfold lookupAny; cases sptLookup n data.toCanonical <;> rfl
            have hvar : exp = .var n := by
              cases exp <;> simp [destVar] at hn; subst hn; rfl
            subst hvar
            have hgn : getVar n s = some w := by rw [wordExp] at hexp; exact hexp
            have d1 := data_inv_reinsert_canonical data s n ⟨hd, by omega⟩
            have d2 := data_inv_filter_gets _ s x d1
            have d3 := data_inv_set_store _ s x w ⟨d2, hcur, hnf _⟩
            rw [e]
            refine data_inv_cons_gets _ (setStore x w s) x (canonicalRegs data n) w
              ⟨d3, hnf _, ?_, ?_, ?_⟩
            · show sptLookup (canonicalRegs data n)
                (sptInsert n (lookupAny n data.toCanonical n) data.toCanonical) = _
              unfold canonicalRegs lookupAny
              cases hl : sptLookup n data.toCanonical with
              | none => simp [sptLookup_sptInsert_same]
              | some c =>
                simp only [Option.getD_some]
                by_cases hcv : c = n
                · subst hcv; exact sptLookup_sptInsert_same _ _ _
                · rw [sptLookup_sptInsert_ne _ _ _ _ hcv]; exact (hd.1.1 n c hl).1
            · simp [setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
            · show getVar (canonicalRegs data n) s = some w
              rw [canonicalRegsCorrect data n s hd]; exact hgn

end Flapjack.Compiler.Backend.WordCse
