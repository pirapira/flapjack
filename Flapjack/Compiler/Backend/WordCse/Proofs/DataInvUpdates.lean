import Flapjack.Compiler.Backend.WordCse.Proofs.DataInvTransport

/-!
# `word_cseProof`: knowledge updates preserve the invariant

Counterpart of the `data_inv` knowledge-update lemmas of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (640-1160): the
If-join merge, fresh register-equivalence and store facts, store-fact
filtering, register tracking and invalidation, and the state updates that do
not touch tracked registers. Each `wf_data` part is the corresponding lemma of
`WfDataPreservation`; each `sem_inv` part goes through `semInv_of_facts`.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace DataInvUpdatesCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end DataInvUpdatesCarrier

/-- `sem_inv` for new knowledge whose register equivalences and store facts
    hold in the state and whose instruction and load facts are old facts
    (Flapjack decomposition of the HOL proofs). -/
theorem semInv_of_facts {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d d' : Knowledge) (s : WordSemStateFiniteExact width C F)
    (htc : ∀ r v, sptLookup r d'.toCanonical = some v → getVar r s = getVar v s)
    (htl : ∀ r v, sptLookup r d'.toLatest = some v → getVar r s = getVar v s)
    (hins : ∀ k v, Misc.BalancedMap.lookup listCmp k d'.instrsMem = some v →
      Misc.BalancedMap.lookup listCmp k d.instrsMem = some v)
    (hgets : ∀ x v, d'.getsMem.lookup x = some v →
      ∃ w, s.store.lookup x = some w ∧ getVar v s = some w)
    (hloads : ∀ k v, Misc.BalancedMap.lookup listCmp k d'.loadsMem = some v →
      Misc.BalancedMap.lookup listCmp k d.loadsMem = some v)
    (h : semInv d s) : semInv d' s := by
  obtain ⟨-, -, h3, h4, h5, h6, -, h8⟩ := h
  exact ⟨htc, htl, fun n c v hk => h3 n c v (hins _ v hk), fun a v hk => h4 a v (hins _ v hk),
    fun op src v hk => h5 op src v (hins _ v hk), fun l v hk => h6 l v (hins _ v hk), hgets,
    fun op a ofs v hk => h8 op a ofs v ⟨hk.1, hloads _ v hk.2⟩⟩

/-- Exact HOL local `ALL_DISTINCT_MAP_FST_FILTER` (`word_cseProof:640-647`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "ALL_DISTINCT_MAP_FST_FILTER"]
theorem all_distinct_map_fst_filter {α β : Type} (l : List (α × β)) (P : α × β → Bool)
    (h : (l.map Prod.fst).Nodup) : ((l.filter P).map Prod.fst).Nodup :=
  (List.Sublist.map Prod.fst List.filter_sublist).nodup h

/-- Lookups in the merged register map come from both sides (Flapjack
    infrastructure). -/
theorem lookup_merge_canonical (d1 d2 : Knowledge) (k v : Nat)
    (h : sptLookup k (mergeData d1 d2).toCanonical = some v) :
    sptLookup k d1.toCanonical = some v ∧ sptLookup k d2.toCanonical = some v := by
  simp only [mergeData, sptLookupInterEq] at h
  cases h1 : sptLookup k d1.toCanonical with
  | none => rw [h1] at h; cases h
  | some w =>
    rw [h1] at h
    simp only at h
    split at h
    · rename_i h2; cases h; exact ⟨rfl, h2⟩
    · cases h

/-- Exact HOL `data_inv_merge_l` (`word_cseProof:649-706`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_merge_l"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_merge_l {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d1 d2 : Knowledge) (s : WordSemStateFiniteExact width C F)
    (h : wfData width d1 ∧ wfData width d2 ∧ semInv d1 s) : dataInv (mergeData d1 d2) s := by
  obtain ⟨w1, w2, hs⟩ := h
  refine ⟨wfData_merge d1 d2 ⟨w1, w2⟩, semInv_of_facts d1 _ s
    (fun r v hr => hs.1 r v (lookup_merge_canonical d1 d2 r v hr).1)
    (fun r v hr => by simp [mergeData] at hr)
    (fun k v hk => ((lookupBmInterEq _ _ k v ⟨w1.2.2.2.2.2.2.2.1, w2.2.2.2.2.2.2.2.1⟩).mp
      (by simpa [mergeData, Misc.BalancedMap.lookup] using hk)).1) (fun x v hx => ?_)
    (fun k v hk => ((lookupBmInterEq _ _ k v ⟨w1.2.2.2.2.2.2.2.2.2.2, w2.2.2.2.2.2.2.2.2.2.2⟩).mp
      (by simpa [mergeData] using hk)).1) hs⟩
  obtain ⟨hmem, -⟩ := List.mem_filter.mp (lookup_some_mem _ _ _ hx)
  exact hs.2.2.2.2.2.2.1 x v (lookup_of_mem_nodup _ _ _ w1.2.2.2.2.2.2.1 hmem)

/-- Exact HOL `data_inv_merge_r` (`word_cseProof:708-773`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_merge_r"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_merge_r {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d1 d2 : Knowledge) (s : WordSemStateFiniteExact width C F)
    (h : wfData width d1 ∧ wfData width d2 ∧ semInv d2 s) : dataInv (mergeData d1 d2) s := by
  obtain ⟨w1, w2, hs⟩ := h
  refine ⟨wfData_merge d1 d2 ⟨w1, w2⟩, semInv_of_facts d2 _ s
    (fun r v hr => hs.1 r v (lookup_merge_canonical d1 d2 r v hr).2)
    (fun r v hr => by simp [mergeData] at hr)
    (fun k v hk => ((lookupBmInterEq _ _ k v ⟨w1.2.2.2.2.2.2.2.1, w2.2.2.2.2.2.2.2.1⟩).mp
      (by simpa [mergeData] using hk)).2) (fun x v hx => ?_)
    (fun k v hk => ((lookupBmInterEq _ _ k v ⟨w1.2.2.2.2.2.2.2.2.2.2, w2.2.2.2.2.2.2.2.2.2.2⟩).mp
      (by simpa [mergeData] using hk)).2) hs⟩
  obtain ⟨-, hcond⟩ := List.mem_filter.mp (lookup_some_mem _ _ _ hx)
  exact hs.2.2.2.2.2.2.1 x v (by simpa using hcond)

/-- Exact HOL `data_inv_insert_to_canonical` (`word_cseProof:829-877`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_to_canonical"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_to_canonical {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x y : Nat)
    (h : dataInv data s ∧ sptLookup x data.toCanonical = none ∧
      sptLookup y (sptInsert x y data.toCanonical) = some y ∧ x % 2 = 1 ∧ y % 2 = 1 ∧
      getVar x s = getVar y s) :
    dataInv { data with toCanonical := sptInsert x y data.toCanonical } s := by
  obtain ⟨⟨hw, hs⟩, hx, hy, ox, oy, hg⟩ := h
  refine ⟨wfData_insert_to_canonical data x y ⟨hw, hx, hy, ox, oy⟩,
    semInv_of_facts data _ s (fun r v hr => ?_) hs.2.1 (fun _ _ hk => hk) hs.2.2.2.2.2.2.1
      (fun _ _ hk => hk) hs⟩
  by_cases hrx : r = x
  · subst hrx; rw [sptLookup_sptInsert_same] at hr; cases hr; exact hg
  · rw [sptLookup_sptInsert_ne _ _ _ _ hrx] at hr; exact hs.1 r v hr

/-- Exact HOL `data_inv_insert_to_latest` (`word_cseProof:879-920`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_to_latest"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_to_latest {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x y : Nat)
    (h : dataInv data s ∧ sptDomain data.toCanonical x ∧ sptDomain data.toCanonical y ∧
      getVar x s = getVar y s) :
    dataInv { data with toLatest := sptInsert x y data.toLatest } s := by
  obtain ⟨⟨hw, hs⟩, dx, dy, hg⟩ := h
  refine ⟨wfData_insert_to_latest data x y ⟨hw, dx, dy⟩,
    semInv_of_facts data _ s hs.1 (fun r v hr => ?_) (fun _ _ hk => hk) hs.2.2.2.2.2.2.1
      (fun _ _ hk => hk) hs⟩
  by_cases hrx : r = x
  · subst hrx; rw [sptLookup_sptInsert_same] at hr; cases hr; exact hg
  · rw [sptLookup_sptInsert_ne _ _ _ _ hrx] at hr; exact hs.2.1 r v hr

/-- Exact HOL local `data_inv_insert_gets` (`word_cseProof:922-978`); HOL
    `ALOOKUP l x` is `List.lookup x l` and `FLOOKUP s.store x` is the
    canonical store lookup. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_gets"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_gets {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (name : WordStoreHOL) (v : Nat)
    (w : WordLocW width)
    (h : dataInv data s ∧ sptLookup v data.toCanonical = none ∧ v % 2 = 1 ∧
      data.getsMem.lookup name = none ∧ s.store.lookup name = some w ∧ getVar v s = some w) :
    dataInv
      { data with
        toCanonical := sptInsert v v data.toCanonical
        toLatest := sptInsert v v data.toLatest
        getsMem := (name, v) :: data.getsMem } s := by
  obtain ⟨⟨hw, hs⟩, hv, ov, hn, hst, hg⟩ := h
  refine ⟨wfData_insert_gets data name v ⟨hw, hv, ov, hn⟩,
    semInv_of_facts data _ s (fun r u hr => ?_) (fun r u hr => ?_) (fun _ _ hk => hk)
      (fun x u hx => ?_) (fun _ _ hk => hk) hs⟩
  · by_cases hrv : r = v
    · subst hrv; rw [sptLookup_sptInsert_same] at hr; cases hr; rfl
    · rw [sptLookup_sptInsert_ne _ _ _ _ hrv] at hr; exact hs.1 r u hr
  · by_cases hrv : r = v
    · subst hrv; rw [sptLookup_sptInsert_same] at hr; cases hr; rfl
    · rw [sptLookup_sptInsert_ne _ _ _ _ hrv] at hr; exact hs.2.1 r u hr
  · simp only [List.lookup_cons] at hx
    split at hx
    · rename_i he
      have : x = name := by simpa using he
      subst this; cases hx; exact ⟨w, hst, hg⟩
    · exact hs.2.2.2.2.2.2.1 x u hx

/-- Exact HOL local `data_inv_filter_gets` (`word_cseProof:980-994`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_filter_gets"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_filter_gets {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x : WordStoreHOL)
    (h : dataInv data s) :
    dataInv { data with getsMem := data.getsMem.filter (fun entry => decide (entry.1 ≠ x)) } s := by
  obtain ⟨hw, hs⟩ := h
  refine ⟨wfData_filter_gets data x hw,
    semInv_of_facts data _ s hs.1 hs.2.1 (fun _ _ hk => hk) (fun y u hy => ?_) (fun _ _ hk => hk) hs⟩
  obtain ⟨hmem, -⟩ := List.mem_filter.mp (lookup_some_mem _ _ _ hy)
  exact hs.2.2.2.2.2.2.1 y u (lookup_of_mem_nodup _ _ _ hw.2.2.2.2.2.2.1 hmem)

/-- Exact HOL local `data_inv_cons_gets` (`word_cseProof:996-1014`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_cons_gets"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_cons_gets {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x : WordStoreHOL) (hv : Nat)
    (w : WordLocW width)
    (h : dataInv data s ∧ data.getsMem.lookup x = none ∧ sptLookup hv data.toCanonical = some hv ∧
      s.store.lookup x = some w ∧ getVar hv s = some w) :
    dataInv { data with getsMem := (x, hv) :: data.getsMem } s := by
  obtain ⟨⟨hw, hs⟩, hn, hself, hst, hg⟩ := h
  refine ⟨wfData_cons_gets data x hv ⟨hw, hn, hself⟩,
    semInv_of_facts data _ s hs.1 hs.2.1 (fun _ _ hk => hk) (fun y u hy => ?_) (fun _ _ hk => hk) hs⟩
  simp only [List.lookup_cons] at hy
  split at hy
  · rename_i he
    have : y = x := by simpa using he
    subst this; cases hy; exact ⟨w, hst, hg⟩
  · exact hs.2.2.2.2.2.2.1 y u hy

/-- Exact HOL `data_inv_set_store` (`word_cseProof:1016-1037`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_store"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_set_store {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x : WordStoreHOL) (w : WordLocW width)
    (h : dataInv data s ∧ x ≠ .currHeap ∧ data.getsMem.lookup x = none) :
    dataInv data (setStore x w s) := by
  obtain ⟨⟨hw, hs⟩, hx, hn⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  have gv : ∀ r, getVar r (setStore x w s) = getVar r s := fun _ => rfl
  have st : ∀ y, y ≠ x → (setStore x w s).store.lookup y = s.store.lookup y := fun y hy => by
    simp [setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hy]
  refine ⟨hw, h1, h2, h3, fun a v hk => ?_, fun op src v hk => ?_, h6, fun y v hy => ?_,
    fun op a ofs v hk => ?_⟩
  · obtain ⟨u, hg, he⟩ := h4 a v hk
    exact ⟨u, hg, evaluateArithAgree a u s _ ⟨he, (hw.2.2.2.1 a v hk).2, rfl⟩⟩
  · obtain ⟨u, he, hg⟩ := h5 op src v hk
    refine ⟨u, ?_, hg⟩
    rw [← he]
    exact Compiler.Backend.WordInst.wordExp_op2_congr _ s op _ _ _ _
      (by rw [wordExp, wordExp]; rfl)
      (by rw [wordExp, wordExp]; simp only [getStore]; exact st _ (Ne.symm hx))
  · obtain ⟨u, hsu, hg⟩ := h7 y v hy
    have hyx : y ≠ x := by rintro rfl; rw [hn] at hy; cases hy
    exact ⟨u, by rw [st y hyx]; exact hsu, hg⟩
  · obtain ⟨u, hg, he⟩ := h8 op a ofs v hk
    exact ⟨u, hg, fun r => evaluateLoadAgree op r a ofs u s _ ⟨he r, hk.1, rfl, rfl, rfl, rfl⟩⟩

/-- Exact HOL local `data_inv_reinsert_canonical` (`word_cseProof:1039-1054`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_reinsert_canonical"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_reinsert_canonical {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (v : Nat)
    (h : dataInv data s ∧ v % 2 = 1) :
    dataInv
      { data with
        toCanonical := sptInsert v (lookupAny v data.toCanonical v) data.toCanonical } s := by
  obtain ⟨⟨hw, hs⟩, ov⟩ := h
  refine ⟨wfData_reinsert_canonical data v ⟨hw, ov⟩,
    semInv_of_facts data _ s (fun r u hr => ?_) hs.2.1 (fun _ _ hk => hk) hs.2.2.2.2.2.2.1
      (fun _ _ hk => hk) hs⟩
  by_cases hrv : r = v
  · subst hrv
    rw [sptLookup_sptInsert_same] at hr
    cases hr
    unfold lookupAny
    split
    · rfl
    · rename_i c hc; exact hs.1 r c hc
  · rw [sptLookup_sptInsert_ne _ _ _ _ hrv] at hr; exact hs.1 r u hr

/-- Exact HOL `empty_data_loads_wipe` (`word_cseProof:1056-1060`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "empty_data_loads_wipe"]
theorem empty_data_loads_wipe :
    ({ emptyData with loadsMem := Misc.BalancedMap.empty } : Knowledge) = emptyData := rfl

/-- Exact HOL `lookup_empty_data` (`word_cseProof:1062-1066`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_empty_data"]
theorem lookup_empty_data (r : Nat) : sptLookup r emptyData.toCanonical = none := rfl

/-- Exact HOL `data_inv_register_read` (`word_cseProof:1068-1075`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_register_read"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_register_read {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat)
    (h : dataInv data s) : dataInv (registerRead data r) s := by
  obtain ⟨hw, hs⟩ := h
  have simps := register_read_simps data r
  refine ⟨wfData_register_read data r hw, semInv_of_facts data _ s (fun x u hx => ?_)
    (fun x u hx => hs.2.1 x u (simps.2.1 ▸ hx)) (fun k u hk => simps.1 ▸ hk)
    (fun x u hx => hs.2.2.2.2.2.2.1 x u (simps.2.2.1 ▸ hx)) (fun k u hk => simps.2.2.2 ▸ hk) hs⟩
  rw [lookup_register_read] at hx
  split at hx
  · rename_i hc; obtain ⟨rfl, -, -⟩ := hc; cases hx; rfl
  · exact hs.1 x u hx

/-- Exact HOL `data_inv_register_reads` (`word_cseProof:1077-1084`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_register_reads"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_register_reads {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (rs : List Nat) (data : Knowledge) (s : WordSemStateFiniteExact width C F),
      dataInv data s → dataInv (registerReads data rs) s
  | [], _, _, h => h
  | r :: rs, data, s, h => data_inv_register_reads rs _ s (data_inv_register_read data s r h)

/-- Exact HOL local `lookup_invalidate_regs_mono` (`word_cseProof:1086-1094`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_invalidate_regs_mono"]
theorem lookup_invalidate_regs_mono (ws : List Nat) (data : Knowledge) (r : Nat)
    (h : sptLookup r data.toCanonical = none) :
    sptLookup r (invalidateRegs data ws).toCanonical = none :=
  lookup_invalidateRegs_none ws data r h

/-- Exact HOL local `lookup_invalidate_regs` (`word_cseProof:1096-1105`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_invalidate_regs"]
theorem lookup_invalidate_regs (ws : List Nat) (data : Knowledge) (r : Nat) (h : r ∈ ws) :
    sptLookup r (invalidateRegs data ws).toCanonical = none :=
  lookup_invalidateRegs_mem ws data r h

/-- Exact HOL local `data_inv_invalidate_regs` (`word_cseProof:1107-1115`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_invalidate_regs"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_invalidate_regs {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (ws : List Nat) (data : Knowledge) (s : WordSemStateFiniteExact width C F),
      dataInv data s → dataInv (invalidateRegs data ws) s
  | [], _, _, h => h
  | r :: ws, data, s, h => by
      simp only [invalidateRegs]
      refine data_inv_invalidate_regs ws _ s ?_
      unfold invalidateData
      split
      · exact h
      · exact dataInvEmpty s

/-- Exact HOL `data_inv_set_fp_var` (`word_cseProof:1117-1125`); HOL bool
    equality is rendered `↔`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_fp_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_set_fp_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (v : Nat) (x : BitVec 64) (s : WordSemStateFiniteExact width C F) :
    (dataInv data (setFpVar v x s) ↔ dataInv data s) := by
  constructor
  · intro h
    exact data_inv_state_agree data (setFpVar v x s) s ⟨h, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    exact data_inv_state_agree data s (setFpVar v x s) ⟨h, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL local `with_locals_insert` (`word_cseProof:1127-1131`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "with_locals_insert"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem with_locals_insert {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (r : Nat) (v : WordLocW width) (l : Spt (WordLocW width)) :
    ({ s with locals := sptInsert r v l } : WordSemStateFiniteExact width C F) =
      setVar r v ({ s with locals := l } : WordSemStateFiniteExact width C F) := rfl

/-- Exact HOL local `data_inv_alist_insert_locals` (`word_cseProof:1133-1143`);
    HOL `alist_insert` is the reviewed `sptAlistInsert`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_alist_insert_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_alist_insert_locals {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (xs : List Nat) (ys : List (WordLocW width)) (data : Knowledge)
      (s : WordSemStateFiniteExact width C F) (l : Spt (WordLocW width)),
      (∀ x ∈ xs, sptLookup x data.toCanonical = none) →
      (dataInv data ({ s with locals := LoopSemStateFiniteExact.sptAlistInsert xs ys l } :
          WordSemStateFiniteExact width C F) ↔
        dataInv data ({ s with locals := l } : WordSemStateFiniteExact width C F))
  | [], _, _, _, _, _ => Iff.rfl
  | _ :: _, [], _, _, _, _ => Iff.rfl
  | x :: xs, y :: ys, data, s, l, h => by
      simp only [LoopSemStateFiniteExact.sptAlistInsert]
      rw [with_locals_insert s x y, data_inv_set_var _ _ x y (h x List.mem_cons_self)]
      exact data_inv_alist_insert_locals xs ys data s l (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- Exact HOL `data_inv_set_vars` (`word_cseProof:1145-1152`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_vars"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_set_vars {width : Nat} [NeZero width] {C : Type} {F : Type}
    (xs : List Nat) (ys : List (WordLocW width)) (data : Knowledge)
    (s : WordSemStateFiniteExact width C F) (h : ∀ x ∈ xs, sptLookup x data.toCanonical = none) :
    (dataInv data (setVars xs ys s) ↔ dataInv data s) :=
  data_inv_alist_insert_locals xs ys data s s.locals h

/-- Exact HOL `evaluate_Move1` (`word_cseProof:1154-1160`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_Move1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_Move1 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (pri r k : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : getVar k s = some w) :
    evaluate (.move pri [(r, k)]) s = (none, setVar r w s) := by
  have hm := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.1
  rw [hm]
  simp [WordSemStateFiniteExact.getVars, h, setVars, LoopSemStateFiniteExact.sptAlistInsert, setVar]

end Flapjack.Compiler.Backend.WordCse
