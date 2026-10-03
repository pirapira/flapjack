import Flapjack.Compiler.Backend.WordCse.Proofs.WellFormedData
import Flapjack.Compiler.Backend.WordCse.RegisterData
import Flapjack.Compiler.Backend.WordCse.Proofs.KnowledgeLemmas
import Flapjack.Compiler.Backend.WordCse.Proofs.ArithmeticKeys
import Flapjack.Compiler.Backend.WordCse.FactProducers
import Flapjack.Compiler.Backend.WordCse.Join
import Flapjack.Compiler.Backend.WordCse.Proofs.IntersectionAccumulator
import Flapjack.Compiler.Backend.WordCse.Proofs.IntersectionInvariant
import Flapjack.Misc.LookupAny
import Flapjack.Compiler.Backend.WordCse.CanonicalMove
import Flapjack.Compiler.Backend.WordCse.CanonicalArith
import Flapjack.Compiler.Backend.WordCse.Transform

/-!
# `word_cseProof`: preservation of the syntactic knowledge invariant

Counterpart of the `wf_data` preservation section of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (2294-2394): the empty
knowledge, load wiping, invalidation, fresh `to_canonical`/`to_latest`
insertions and register tracking keep `wf_data`. HOL's `ODD x` is rendered
`x % 2 = 1`, as in the reviewed `wfData`.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

section Helpers

/-- A `to_canonical` self-mapping survives a fresh insertion (Flapjack
    infrastructure). -/
theorem self_insert_fresh {tc : Spt Nat} {x y v : Nat} (hx : sptLookup x tc = none)
    (hv : sptLookup v tc = some v) : sptLookup v (sptInsert x y tc) = some v := by
  have hne : v ≠ x := by rintro rfl; rw [hx] at hv; cases hv
  rw [sptLookup_sptInsert_ne _ _ _ _ hne, hv]

end Helpers

/-- Exact HOL `wf_data_empty` (`word_cseProof:2294-2298`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_empty"
  (words_as_type_indexed_bitvec)]
theorem wfData_empty {width : Nat} [NeZero width] : wfData width emptyData := by
  simp [wfData, emptyData, Misc.BalancedMap.empty, Misc.BalancedMap.lookup,
    Misc.BalancedMap.invariant]

/-- Exact HOL `wf_data_loads_wipe` (`word_cseProof:2301-2305`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_loads_wipe"
  (words_as_type_indexed_bitvec)]
theorem wfData_loads_wipe {width : Nat} [NeZero width] (data : Knowledge)
    (h : wfData width data) : wfData width { data with loadsMem := Misc.BalancedMap.empty } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, _, _⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_⟩ <;>
    simp [Misc.BalancedMap.empty, Misc.BalancedMap.lookup, Misc.BalancedMap.invariant]

/-- Exact HOL `wf_data_invalidate` (`word_cseProof:2308-2312`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_invalidate"
  (words_as_type_indexed_bitvec)]
theorem wfData_invalidate {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (h : wfData width data) : wfData width (invalidateData data r) := by
  unfold invalidateData
  split
  · exact h
  · exact wfData_empty

/-- Exact HOL `wf_data_invalidate_regs` (`word_cseProof:2314-2318`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_invalidate_regs"
  (words_as_type_indexed_bitvec)]
theorem wfData_invalidate_regs {width : Nat} [NeZero width] :
    ∀ (rs : List Nat) (data : Knowledge), wfData width data → wfData width (invalidateRegs data rs)
  | [], _, h => h
  | r :: rs, data, h => wfData_invalidate_regs rs _ (wfData_invalidate data r h)

/-- Exact HOL `wf_data_insert_to_canonical` (`word_cseProof:2322-2363`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_to_canonical"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_to_canonical {width : Nat} [NeZero width] (data : Knowledge) (x y : Nat)
    (h : wfData width data ∧ sptLookup x data.toCanonical = none ∧
      sptLookup y (sptInsert x y data.toCanonical) = some y ∧ x % 2 = 1 ∧ y % 2 = 1) :
    wfData width { data with toCanonical := sptInsert x y data.toCanonical } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hx, hy, ox, oy⟩ := h
  have keep : ∀ v, sptLookup v data.toCanonical = some v →
      sptLookup v (sptInsert x y data.toCanonical) = some v := fun v hv => self_insert_fresh hx hv
  have dom : ∀ r, sptDomain data.toCanonical r → sptDomain (sptInsert x y data.toCanonical) r := by
    intro r hr
    by_cases hrx : r = x
    · subst hrx; simp [sptDomain, sptLookup_sptInsert_same]
    · simpa [sptDomain, sptLookup_sptInsert_ne _ _ _ _ hrx] using hr
  refine ⟨?_, ?_, fun k v hk => keep v (h3 k v hk), ?_, fun op src v hk => keep src (h5 op src v hk),
    fun st v hk => keep v (h6 st v hk), h7, h8, fun k v hk => keep v (h9 k v hk),
    fun op a ofs v hk => keep a (h10 op a ofs v hk), h11⟩
  · intro r v hr
    by_cases hrx : r = x
    · subst hrx
      rw [sptLookup_sptInsert_same] at hr
      cases hr
      exact ⟨hy, ox, oy⟩
    · rw [sptLookup_sptInsert_ne _ _ _ _ hrx] at hr
      obtain ⟨hv, or, ov⟩ := h1 r v hr
      exact ⟨keep v hv, or, ov⟩
  · intro r v hr
    obtain ⟨d1, d2⟩ := h2 r v hr
    exact ⟨dom r d1, dom v d2⟩
  · intro op v hk
    obtain ⟨hn, hc⟩ := h4 op v hk
    exact ⟨fun reg hreg => keep reg (hn reg hreg), hc⟩

/-- Exact HOL `wf_data_insert_to_latest` (`word_cseProof:2366-2376`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_to_latest"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_to_latest {width : Nat} [NeZero width] (data : Knowledge) (x y : Nat)
    (h : wfData width data ∧ sptDomain data.toCanonical x ∧ sptDomain data.toCanonical y) :
    wfData width { data with toLatest := sptInsert x y data.toLatest } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, dx, dy⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  intro r v hr
  by_cases hrx : r = x
  · subst hrx
    rw [sptLookup_sptInsert_same] at hr
    cases hr
    exact ⟨dx, dy⟩
  · rw [sptLookup_sptInsert_ne _ _ _ _ hrx] at hr
    exact h2 r v hr

/-- Exact HOL `wf_data_register_read` (`word_cseProof:2378-2382`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_register_read"
  (words_as_type_indexed_bitvec)]
theorem wfData_register_read {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (h : wfData width data) : wfData width (registerRead data r) := by
  unfold registerRead keepData
  split
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at hc
    exact wfData_insert_to_canonical data r r
      ⟨h, hc.2, sptLookup_sptInsert_same _ _ _, by omega, by omega⟩
  · exact h

/-- Exact HOL `wf_data_register_reads` (`word_cseProof:2386-2390`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_register_reads"
  (words_as_type_indexed_bitvec)]
theorem wfData_register_reads {width : Nat} [NeZero width] :
    ∀ (rs : List Nat) (data : Knowledge), wfData width data → wfData width (registerReads data rs)
  | [], _, h => h
  | r :: rs, data, h => wfData_register_reads rs _ (wfData_register_read data r h)

section InsertFacts

/-- Inserting an instruction fact `key ↦ r` with a self-mapped holder keeps
    `wf_data` when every arithmetic or `OpCurrHeap` instruction with that key
    satisfies the corresponding clause (Flapjack infrastructure). -/
theorem wfData_insert_instrs_key {width : Nat} [NeZero width] (data : Knowledge) (key : List Nat)
    (r : Nat) (h : wfData width data) (hr : sptLookup r data.toCanonical = some r)
    (ha : ∀ a : Compiler.Encoders.Asm.HolArith width, instToNumList (.arith a) = key →
      inNamesSet a data.toCanonical ∧ canMemArith a = true)
    (hb : ∀ op src, opCurrHeapToNumList op src = key → sptLookup src data.toCanonical = some src) :
    wfData width { data with instrsMem := Misc.BalancedMap.insert listCmp key r data.instrsMem } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have ins := fun k => lookup_insert_listCmp k key r data.instrsMem h8
  refine ⟨h1, h2, ?_, ?_, ?_, h6, h7, (ins key).1, h9, h10, h11⟩
  · intro k v hk
    rw [(ins k).2] at hk
    split at hk
    · cases hk; exact hr
    · exact h3 k v hk
  · intro a v hk
    rw [(ins _).2] at hk
    split at hk
    · exact ha a (by assumption)
    · exact h4 a v hk
  · intro op src v hk
    rw [(ins _).2] at hk
    split at hk
    · exact hb op src (by assumption)
    · exact h5 op src v hk

/-- Exact HOL local `wf_data_insert_instrs_Const` (`word_cseProof:2396-2410`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_Const"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_instrs_Const {width : Nat} [NeZero width] (data : Knowledge) (r n : Nat)
    (w : BitVec width) (h : wfData width data ∧ sptLookup r data.toCanonical = some r) :
    wfData width { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (instToNumList (.const n w)) r data.instrsMem } :=
  wfData_insert_instrs_key data _ r h.1 h.2
    (fun a ha => by simp [instToNumList] at ha)
    (fun op src hk => by simp [instToNumList, opCurrHeapToNumList] at hk)

/-- Exact HOL local `wf_data_insert_instrs_Arith` (`word_cseProof:2412-2433`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_Arith"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_instrs_Arith {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (a : Compiler.Encoders.Asm.HolArith width)
    (h : wfData width data ∧ sptLookup r data.toCanonical = some r ∧
      canMemArith a = true ∧ inNamesSet a data.toCanonical) :
    wfData width { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (instToNumList (.arith a)) r data.instrsMem } := by
  obtain ⟨hw, hr, hc, hn⟩ := h
  refine wfData_insert_instrs_key data _ r hw hr (fun a2 ha2 => ?_)
    (fun op src hk => by simp [instToNumList, opCurrHeapToNumList] at hk)
  simp only [instToNumList, List.cons.injEq, true_and] at ha2
  obtain ⟨hc2, hreads, -⟩ := arithKeysEq (C := Unit) (F := Unit) a a2 ⟨hc, ha2.symm⟩
  exact ⟨fun reg hreg => hn reg (hreads ▸ hreg), hc2⟩

/-- Exact HOL local `wf_data_insert_instrs_OpCurrHeap` (`word_cseProof:2435-2450`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_OpCurrHeap"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_instrs_OpCurrHeap {width : Nat} [NeZero width] (data : Knowledge)
    (r : Nat) (op : BinOp) (src : Nat)
    (h : wfData width data ∧ sptLookup r data.toCanonical = some r ∧
      sptLookup src data.toCanonical = some src) :
    wfData width { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (opCurrHeapToNumList op src) r data.instrsMem } := by
  refine wfData_insert_instrs_key data _ r h.1 h.2.1
    (fun a ha => by simp [instToNumList, opCurrHeapToNumList] at ha) (fun op2 src2 hk => ?_)
  simp only [opCurrHeapToNumList, List.cons.injEq, Nat.add_right_cancel_iff, and_true] at hk
  rw [hk.2.2]; exact h.2.2

/-- Exact HOL local `wf_data_insert_instrs_LocValue` (`word_cseProof:2452-2465`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_LocValue"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_instrs_LocValue {width : Nat} [NeZero width] (data : Knowledge) (r l : Nat)
    (h : wfData width data ∧ sptLookup r data.toCanonical = some r) :
    wfData width { data with instrsMem :=
      Misc.BalancedMap.insert listCmp [48, l] r data.instrsMem } :=
  wfData_insert_instrs_key data _ r h.1 h.2
    (fun a ha => by simp [instToNumList] at ha)
    (fun op src hk => by simp [opCurrHeapToNumList] at hk)

/-- Exact HOL local `wf_data_insert_loads` (`word_cseProof:2467-2485`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_loads"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_loads {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (op : Compiler.Encoders.Asm.HolMemop) (a : Nat) (ofs : BitVec width)
    (h : wfData width data ∧ sptLookup r data.toCanonical = some r ∧
      sptLookup a data.toCanonical = some a) :
    wfData width { data with loadsMem :=
      Misc.BalancedMap.insert listCmp (loadToNumList op a ofs) r data.loadsMem } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hr, ha⟩ := h
  have ins := fun k => lookup_insert_listCmp k (loadToNumList op a ofs) r data.loadsMem h11
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, (ins [0]).1⟩
  · intro k v hk
    rw [(ins k).2] at hk
    split at hk
    · cases hk; exact hr
    · exact h9 k v hk
  · intro op2 a2 ofs2 v hk
    rw [(ins _).2] at hk
    split at hk
    · rename_i heq
      simp only [loadToNumList, List.cons.injEq, Nat.add_right_cancel_iff] at heq
      rw [heq.2.1]; exact ha
    · exact h10 op2 a2 ofs2 v hk

end InsertFacts

section Producers

/-- `ALOOKUP` finds only stored pairs (Flapjack infrastructure). -/
theorem lookup_some_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: l, k, v, h => by
      simp only [List.lookup_cons] at h
      split at h
      · rename_i hk
        cases h
        have : k = a := by simpa using hk
        subst this; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookup_some_mem l k v h)

/-- With distinct keys, `ALOOKUP` finds every stored pair (Flapjack
    infrastructure). -/
theorem lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (a, b) :: l, k, v, hnd, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.lookup_cons]
      rcases List.mem_cons.mp h with he | hm
      · cases he; simp
      · have hka : k ≠ a := by
          rintro rfl; exact hnd.1 (List.mem_map.mpr ⟨(k, v), hm, rfl⟩)
        have : (k == a) = false := by simpa using hka
        rw [this]
        exact lookup_of_mem_nodup l k v hnd.2 hm

/-- `wf_data` reads `to_canonical` only through lookups (Flapjack
    infrastructure). -/
theorem wfData_canonical_congr {width : Nat} [NeZero width] (data : Knowledge) (tc : Spt Nat)
    (heq : ∀ k, sptLookup k tc = sptLookup k data.toCanonical) (h : wfData width data) :
    wfData width { data with toCanonical := tc } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨fun r v hr => ?_, fun r v hr => ?_, fun k v hk => ?_, fun a v hk => ?_,
    fun op src v hk => ?_, fun st v hk => ?_, h7, h8, fun k v hk => ?_,
    fun op a ofs v hk => ?_, h11⟩
  · rw [heq] at hr
    obtain ⟨hv, o1, o2⟩ := h1 r v hr
    exact ⟨by rw [heq]; exact hv, o1, o2⟩
  · simp only [sptDomain, heq]; exact h2 r v hr
  · rw [heq]; exact h3 k v hk
  · obtain ⟨hn, hc⟩ := h4 a v hk
    exact ⟨fun reg hreg => by rw [heq]; exact hn reg hreg, hc⟩
  · rw [heq]; exact h5 op src v hk
  · rw [heq]; exact h6 st v hk
  · rw [heq]; exact h9 k v hk
  · rw [heq]; exact h10 op a ofs v hk

/-- The hit case of the fact producers: re-pointing a fresh odd destination at
    a self-mapped odd holder keeps `wf_data` (Flapjack infrastructure). -/
theorem wfData_repoint {width : Nat} [NeZero width] (data : Knowledge) (r r' : Nat)
    (h : wfData width data) (hr : sptLookup r data.toCanonical = none) (odd : r % 2 = 1)
    (hself : sptLookup r' data.toCanonical = some r') :
    wfData width
      { data with
        toCanonical := sptInsert r r' data.toCanonical
        toLatest := sptInsert r' r data.toLatest } := by
  have odd' := (h.1 r' r' hself).2.2
  have h1 := wfData_insert_to_canonical data r r'
    ⟨h, hr, self_insert_fresh hr hself, odd, odd'⟩
  have dom : ∀ x, sptLookup x (sptInsert r r' data.toCanonical) = some x →
      sptDomain (sptInsert r r' data.toCanonical) x := fun x hx => by simp [sptDomain, hx]
  refine wfData_insert_to_latest _ r' r ⟨h1, dom r' (self_insert_fresh hr hself), ?_⟩
  simp [sptDomain, sptLookup_sptInsert_same]

/-- Exact HOL `wf_add_to_data_aux` (`word_cseProof:2487-2539`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_data_aux"
  (words_as_type_indexed_bitvec)]
theorem wf_add_to_data_aux {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (i : List Nat) (p : WordLangProgHOL (BitVec width)) (data' : Knowledge)
    (p' : WordLangProgHOL (BitVec width))
    (h : wfData width data ∧ sptLookup r data.toCanonical = none ∧
      addToDataAux data r i p = (data', p') ∧
      (¬ r % 2 = 0 → wfData width
        { { data with toCanonical := sptInsert r r data.toCanonical } with
          instrsMem := Misc.BalancedMap.insert listCmp i r
            ({ data with toCanonical := sptInsert r r data.toCanonical } : Knowledge).instrsMem })) :
    wfData width data' := by
  obtain ⟨hw, hr, he, hmiss⟩ := h
  unfold addToDataAux at he
  split at he
  · rename_i r' hl
    split at he
    · cases he; exact hw
    · cases he
      exact wfData_repoint data r r' hw hr (by omega) (hw.2.2.1 i r' hl)
  · split at he
    · cases he; exact hw
    · rename_i hev
      cases he
      have := hmiss hev
      exact wfData_insert_to_latest _ r r ⟨this, by simp [sptDomain, sptLookup_sptInsert_same],
        by simp [sptDomain, sptLookup_sptInsert_same]⟩

/-- Exact HOL `wf_add_to_data_const` (`word_cseProof:2541-2598`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_data_const"
  (words_as_type_indexed_bitvec)]
theorem wf_add_to_data_const {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (w : BitVec width) (data' : Knowledge) (p' : WordLangProgHOL (BitVec width))
    (h : wfData width data ∧ sptLookup r data.toCanonical = none ∧ ¬ r % 2 = 0 ∧
      addToDataConst data r w = (data', p')) :
    wfData width data' := by
  obtain ⟨hw, hr, hev, he⟩ := h
  unfold addToDataConst at he
  dsimp only at he
  split at he
  · rename_i r' hl
    cases he
    exact wfData_repoint data r r' hw hr (by omega) (hw.2.2.1 _ r' hl)
  · cases he
    have h1 := wfData_insert_to_canonical data r r
      ⟨hw, hr, sptLookup_sptInsert_same _ _ _, by omega, by omega⟩
    have h2 := wfData_insert_instrs_Const _ r r w ⟨h1, sptLookup_sptInsert_same _ _ _⟩
    exact wfData_insert_to_latest _ r r ⟨h2, by simp [sptDomain, sptLookup_sptInsert_same],
      by simp [sptDomain, sptLookup_sptInsert_same]⟩

/-- Exact HOL `wf_add_to_load_aux` (`word_cseProof:2600-2650`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_load_aux"
  (words_as_type_indexed_bitvec)]
theorem wf_add_to_load_aux {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (i : List Nat) (p : WordLangProgHOL (BitVec width)) (data' : Knowledge)
    (p' : WordLangProgHOL (BitVec width))
    (h : wfData width data ∧ sptLookup r data.toCanonical = none ∧
      addToLoadAux data r i p = (data', p') ∧
      (¬ r % 2 = 0 → wfData width
        { { data with toCanonical := sptInsert r r data.toCanonical } with
          loadsMem := Misc.BalancedMap.insert listCmp i r
            ({ data with toCanonical := sptInsert r r data.toCanonical } : Knowledge).loadsMem })) :
    wfData width data' := by
  obtain ⟨hw, hr, he, hmiss⟩ := h
  unfold addToLoadAux at he
  split at he
  · rename_i r' hl
    split at he
    · cases he; exact hw
    · cases he
      exact wfData_repoint data r r' hw hr (by omega) (hw.2.2.2.2.2.2.2.2.1 i r' hl)
  · split at he
    · cases he; exact hw
    · rename_i hev
      cases he
      have := hmiss hev
      exact wfData_insert_to_latest _ r r ⟨this, by simp [sptDomain, sptLookup_sptInsert_same],
        by simp [sptDomain, sptLookup_sptInsert_same]⟩

/-- Exact HOL local `wf_data_insert_gets` (`word_cseProof:2652-2668`); HOL
    `ALOOKUP l x` is `List.lookup x l`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_gets"
  (words_as_type_indexed_bitvec)]
theorem wfData_insert_gets {width : Nat} [NeZero width] (data : Knowledge) (name : WordStoreHOL)
    (v : Nat)
    (h : wfData width data ∧ sptLookup v data.toCanonical = none ∧ v % 2 = 1 ∧
      data.getsMem.lookup name = none) :
    wfData width
      { data with
        toCanonical := sptInsert v v data.toCanonical
        toLatest := sptInsert v v data.toLatest
        getsMem := (name, v) :: data.getsMem } := by
  obtain ⟨hw, hv, odd, hn⟩ := h
  have h1 := wfData_insert_to_canonical data v v
    ⟨hw, hv, sptLookup_sptInsert_same _ _ _, odd, odd⟩
  have h2 := wfData_insert_to_latest _ v v ⟨h1, by simp [sptDomain, sptLookup_sptInsert_same],
    by simp [sptDomain, sptLookup_sptInsert_same]⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := h2
  refine ⟨g1, g2, g3, g4, g5, fun st w hst => ?_, ?_, g8, g9, g10, g11⟩
  · simp only [List.lookup_cons] at hst
    split at hst
    · cases hst; exact sptLookup_sptInsert_same _ _ _
    · exact g6 st w hst
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, g7⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    have := List.lookup_eq_none_iff.mp hn p hp
    simp at this

/-- Exact HOL local `wf_data_filter_gets` (`word_cseProof:2670-2680`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_filter_gets"
  (words_as_type_indexed_bitvec)]
theorem wfData_filter_gets {width : Nat} [NeZero width] (data : Knowledge) (x : WordStoreHOL)
    (h : wfData width data) :
    wfData width { data with getsMem := data.getsMem.filter (fun entry => decide (entry.1 ≠ x)) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun st w hst => ?_, ?_, h8, h9, h10, h11⟩
  · obtain ⟨hmem, -⟩ := List.mem_filter.mp (lookup_some_mem _ _ _ hst)
    exact h6 st w (lookup_of_mem_nodup _ _ _ h7 hmem)
  · exact (List.Sublist.map Prod.fst List.filter_sublist).nodup h7

/-- Exact HOL local `wf_data_cons_gets` (`word_cseProof:2682-2693`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_cons_gets"
  (words_as_type_indexed_bitvec)]
theorem wfData_cons_gets {width : Nat} [NeZero width] (data : Knowledge) (x : WordStoreHOL)
    (hv : Nat)
    (h : wfData width data ∧ data.getsMem.lookup x = none ∧ sptLookup hv data.toCanonical = some hv) :
    wfData width { data with getsMem := (x, hv) :: data.getsMem } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hn, hs⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun st w hst => ?_, ?_, h8, h9, h10, h11⟩
  · simp only [List.lookup_cons] at hst
    split at hst
    · cases hst; exact hs
    · exact h6 st w hst
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, h7⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    have := List.lookup_eq_none_iff.mp hn p hp
    simp at this

/-- Exact HOL local `wf_data_reinsert_canonical` (`word_cseProof:2695-2712`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_reinsert_canonical"
  (words_as_type_indexed_bitvec)]
theorem wfData_reinsert_canonical {width : Nat} [NeZero width] (data : Knowledge) (v : Nat)
    (h : wfData width data ∧ v % 2 = 1) :
    wfData width
      { data with
        toCanonical := sptInsert v (lookupAny v data.toCanonical v) data.toCanonical } := by
  obtain ⟨hw, odd⟩ := h
  unfold lookupAny
  split
  · rename_i hn
    exact wfData_insert_to_canonical data v v ⟨hw, hn, sptLookup_sptInsert_same _ _ _, odd, odd⟩
  · rename_i u hu
    refine wfData_canonical_congr data _ (fun k => ?_) hw
    by_cases hk : k = v
    · subst hk; rw [sptLookup_sptInsert_same, hu]
    · rw [sptLookup_sptInsert_ne _ _ _ _ hk]

/-- Exact HOL `wf_data_merge` (`word_cseProof:2714-2759`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_merge"
  (words_as_type_indexed_bitvec)]
theorem wfData_merge {width : Nat} [NeZero width] (d1 d2 : Knowledge)
    (h : wfData width d1 ∧ wfData width d2) : wfData width (mergeData d1 d2) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩⟩ := h
  have tc : ∀ k v, sptLookup k (sptInterEq d1.toCanonical d2.toCanonical) = some v ↔
      sptLookup k d1.toCanonical = some v ∧ sptLookup k d2.toCanonical = some v := by
    intro k v
    rw [sptLookupInterEq]
    cases h1 : sptLookup k d1.toCanonical with
    | none => simp
    | some w =>
      by_cases h2 : sptLookup k d2.toCanonical = some w
      · simp [h2]
      · simp only [h2, if_false, reduceCtorEq, false_iff, not_and, Option.some.injEq]
        rintro rfl; exact h2
  have bm := fun (m1 m2 : Misc.BalancedMap.Map (List Nat) Nat) (i1 : Misc.BalancedMap.invariant listCmp m1)
      (i2 : Misc.BalancedMap.invariant listCmp m2) k v =>
    lookupBmInterEq m1 m2 k v ⟨i1, i2⟩
  refine ⟨fun r v hr => ?_, fun r v hr => ?_, fun k v hk => ?_, fun a v hk => ?_,
    fun op src v hk => ?_, fun st v hk => ?_, ?_, invariantBmInterEq _ _ ⟨a8, b8⟩,
    fun k v hk => ?_, fun op a ofs v hk => ?_, invariantBmInterEq _ _ ⟨a11, b11⟩⟩
  · obtain ⟨h1, h2⟩ := (tc r v).mp hr
    obtain ⟨s1, o1, o2⟩ := a1 r v h1
    exact ⟨(tc v v).mpr ⟨s1, (b1 r v h2).1⟩, o1, o2⟩
  · simp [mergeData] at hr
  · obtain ⟨h1, h2⟩ := (bm _ _ a8 b8 k v).mp hk
    exact (tc v v).mpr ⟨a3 k v h1, b3 k v h2⟩
  · obtain ⟨h1, h2⟩ := (bm _ _ a8 b8 _ v).mp hk
    obtain ⟨n1, c1⟩ := a4 a v h1
    exact ⟨fun reg hreg => (tc reg reg).mpr ⟨n1 reg hreg, (b4 a v h2).1 reg hreg⟩, c1⟩
  · obtain ⟨h1, h2⟩ := (bm _ _ a8 b8 _ v).mp hk
    exact (tc src src).mpr ⟨a5 op src v h1, b5 op src v h2⟩
  · obtain ⟨hmem1, hcond⟩ := List.mem_filter.mp (lookup_some_mem _ _ _ hk)
    have hd2 : d2.getsMem.lookup st = some v := by simpa using hcond
    exact (tc v v).mpr ⟨a6 st v (lookup_of_mem_nodup _ _ _ a7 hmem1), b6 st v hd2⟩
  · exact (List.Sublist.map Prod.fst List.filter_sublist).nodup a7
  · obtain ⟨h1, h2⟩ := (bm _ _ a11 b11 k v).mp hk
    exact (tc v v).mpr ⟨a9 k v h1, b9 k v h2⟩
  · obtain ⟨h1, h2⟩ := (bm _ _ a11 b11 _ v).mp hk
    exact (tc a a).mpr ⟨a10 op a ofs v h1, b10 op a ofs v h2⟩

end Producers

section Moves

/-- Lookup in the tail-first `map_insert`: the first binding of a key in the
    list wins (Flapjack infrastructure). -/
theorem sptLookup_mapInsert {α : Type} :
    ∀ (ps : List (Nat × α)) (t : Spt α) (k : Nat),
      sptLookup k (mapInsert ps t) = match ps.lookup k with
        | some v => some v
        | none => sptLookup k t
  | [], _, _ => rfl
  | (a, b) :: ps, t, k => by
      simp only [mapInsert, List.lookup_cons]
      by_cases hk : k = a
      · subst hk; simp [sptLookup_sptInsert_same]
      · have : (k == a) = false := by simpa using hk
        rw [this, sptLookup_sptInsert_ne _ _ _ _ hk]
        exact sptLookup_mapInsert ps t k

/-- Exact HOL local `wf_data_move_pairs` (`word_cseProof:2761-2798`); HOL
    `EVERY (λ(x,y). P x y) ps` is `∀ p ∈ ps, P p.1 p.2`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_move_pairs"
  (words_as_type_indexed_bitvec)]
theorem wfData_move_pairs {width : Nat} [NeZero width] (ps : List (Nat × Nat)) (data : Knowledge)
    (h : wfData width data ∧ ∀ p ∈ ps, sptLookup p.1 data.toCanonical = none ∧
      sptLookup p.2 data.toCanonical = some p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1) :
    wfData width
      { data with
        toCanonical := mapInsert ps data.toCanonical
        toLatest := mapInsert (ps.map (fun p => (p.2, p.1))) data.toLatest } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hps⟩ := h
  -- a register with a canonical binding is never a destination of `ps`
  have notKey : ∀ v w, sptLookup v data.toCanonical = some w → ps.lookup v = none := by
    intro v w hv
    refine List.lookup_eq_none_iff.mpr (fun p hp => ?_)
    have := (hps p hp).1
    simp only [bne_iff_ne, ne_eq]
    rintro rfl; rw [this] at hv; cases hv
  have keep : ∀ v, sptLookup v data.toCanonical = some v →
      sptLookup v (mapInsert ps data.toCanonical) = some v := fun v hv => by
    rw [sptLookup_mapInsert, notKey v v hv]; exact hv
  have dom : ∀ r, sptDomain data.toCanonical r → sptDomain (mapInsert ps data.toCanonical) r := by
    intro r hr
    simp only [sptDomain, sptLookup_mapInsert] at hr ⊢
    split <;> simp_all
  refine ⟨fun r v hr => ?_, fun r v hr => ?_, fun k v hk => keep v (h3 k v hk), fun a v hk => ?_,
    fun op src v hk => keep src (h5 op src v hk), fun st v hk => keep v (h6 st v hk), h7, h8,
    fun k v hk => keep v (h9 k v hk), fun op a ofs v hk => keep a (h10 op a ofs v hk), h11⟩
  · rw [sptLookup_mapInsert] at hr
    cases hw : ps.lookup r with
    | some w =>
      rw [hw] at hr
      obtain rfl : w = v := Option.some.inj hr
      obtain ⟨-, hy, ox, oy⟩ := hps (r, w) (lookup_some_mem _ _ _ hw)
      exact ⟨keep w hy, ox, oy⟩
    | none =>
      rw [hw] at hr
      obtain ⟨hv, o1, o2⟩ := h1 r v hr
      exact ⟨keep v hv, o1, o2⟩
  · rw [sptLookup_mapInsert] at hr
    cases hw : (ps.map (fun p => (p.2, p.1))).lookup r with
    | some w =>
      rw [hw] at hr
      cases hr
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (lookup_some_mem _ _ _ hw)
      obtain ⟨-, hy, -, -⟩ := hps p hp
      have e2 : p.2 = r := congrArg Prod.fst hpe
      have e1 : p.1 = v := congrArg Prod.snd hpe
      refine ⟨by rw [← e2]; simp [sptDomain, keep p.2 hy], ?_⟩
      simp only [sptDomain, sptLookup_mapInsert, ← e1]
      have hsome : (ps.lookup p.1).isSome := List.lookup_isSome_iff.mpr ⟨p, hp, by simp⟩
      cases hl : ps.lookup p.1 with
      | some _ => rfl
      | none => rw [hl] at hsome; cases hsome
    | none =>
      rw [hw] at hr
      obtain ⟨d1, d2⟩ := h2 r v hr
      exact ⟨dom r d1, dom v d2⟩
  · obtain ⟨hn, hc⟩ := h4 a v hk
    exact ⟨fun reg hreg => keep reg (hn reg hreg), hc⟩

/-- Exact HOL `wf_canonicalMoveRegs` (`word_cseProof:2800-2830`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_canonicalMoveRegs"
  (words_as_type_indexed_bitvec)]
theorem wf_canonicalMoveRegs {width : Nat} [NeZero width] (data : Knowledge) (rs : List (Nat × Nat))
    (h : wfData width data) : wfData width (canonicalMoveRegs data rs) := by
  unfold canonicalMoveRegs
  dsimp only
  split
  · rename_i hall
    have hw := wfData_register_reads (rs.map Prod.snd) data h
    refine wfData_move_pairs _ _ ⟨hw, fun p hp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hqm, hodd⟩ := List.mem_filter.mp hq
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hodd
    have hkeep := List.all_eq_true.mp hall q.1 (List.mem_map.mpr ⟨q, hqm, rfl⟩)
    simp only [keepData, Option.isNone_iff_eq_none] at hkeep
    have hsrc : ∃ c, sptLookup q.2 (registerReads data (rs.map Prod.snd)).toCanonical = some c := by
      rw [lookup_register_reads]
      split
      · exact ⟨_, rfl⟩
      · rename_i hc
        cases hl : sptLookup q.2 data.toCanonical with
        | some c => exact ⟨c, rfl⟩
        | none =>
          exact absurd ⟨List.mem_map.mpr ⟨q, hqm, rfl⟩, hodd.2, hl⟩ hc
    obtain ⟨c, hc⟩ := hsrc
    have hcan : canonicalRegs (registerReads data (rs.map Prod.snd)) q.2 = c := by
      simp [canonicalRegs, hc]
    obtain ⟨hself, -, oc⟩ := hw.1 q.2 c hc
    refine ⟨hkeep, ?_, by omega, ?_⟩ <;> simp only [hcan]
    · exact hself
    · exact oc
  · exact wfData_empty

/-- Exact HOL local `canonicalRegs_self_or_fresh_wf` (`word_cseProof:2832-2843`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_self_or_fresh_wf"
  (words_as_type_indexed_bitvec)]
theorem canonicalRegs_self_or_fresh_wf {width : Nat} [NeZero width] (data : Knowledge) (x : Nat)
    (h : wfData width data) :
    sptLookup (canonicalRegs data x) data.toCanonical = some (canonicalRegs data x) ∨
      sptLookup (canonicalRegs data x) data.toCanonical = none := by
  unfold canonicalRegs
  cases hx : sptLookup x data.toCanonical with
  | none => right; simpa using hx
  | some c => left; simpa using (h.1 x c hx).1

/-- Exact HOL local `canonicalRegs'_self_or_fresh_wf` (`word_cseProof:2846`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_self_or_fresh_wf"
  (words_as_type_indexed_bitvec)]
theorem canonicalRegs'_self_or_fresh_wf {width : Nat} [NeZero width] (data : Knowledge)
    (r1 x : Nat) (h : wfData width data ∧ sptLookup r1 data.toCanonical = none) :
    sptLookup (canonicalRegs' r1 data x) data.toCanonical = some (canonicalRegs' r1 data x) ∨
      sptLookup (canonicalRegs' r1 data x) data.toCanonical = none := by
  obtain ⟨hw, hr1⟩ := h
  unfold canonicalRegs'
  dsimp only
  split
  · rename_i heq
    unfold canonicalRegs at heq
    cases hx : sptLookup x data.toCanonical with
    | none => right; rfl
    | some c =>
      rw [hx] at heq
      simp only [Option.getD_some] at heq
      subst heq
      rw [(hw.1 x c hx).1] at hr1
      cases hr1
  · exact canonicalRegs_self_or_fresh_wf data x hw

/-- Exact HOL local `in_names_set_insert_self` (`word_cseProof:2861-2865`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_insert_self"
  (words_as_type_indexed_bitvec)]
theorem inNamesSet_insert_self {width : Nat} [NeZero width] (a : Compiler.Encoders.Asm.HolArith width)
    (tc : Spt Nat) (x : Nat) (h : inNamesSet a tc) : inNamesSet a (sptInsert x x tc) := by
  intro reg hreg
  by_cases hx : reg = x
  · subst hx; exact sptLookup_sptInsert_same _ _ _
  · rw [sptLookup_sptInsert_ne _ _ _ _ hx]; exact h reg hreg

/-- Exact HOL local `in_names_set_register_reads` (`word_cseProof:2867-2879`);
    HOL `EVERY P l` is `∀ w ∈ l, P w` and `ODD w` is `w % 2 = 1`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_register_reads"
  (words_as_type_indexed_bitvec)]
theorem inNamesSet_register_reads {width : Nat} [NeZero width]
    (a : Compiler.Encoders.Asm.HolArith width) (data : Knowledge)
    (h : (∀ w ∈ arithReads a, w % 2 = 1) ∧
      ∀ w ∈ arithReads a, sptLookup w data.toCanonical = none ∨
        sptLookup w data.toCanonical = some w) :
    inNamesSet a (registerReads data (arithReads a)).toCanonical := by
  intro reg hreg
  rw [lookup_register_reads]
  split
  · rfl
  · rename_i hc
    rcases h.2 reg hreg with hn | hs
    · exact absurd ⟨hreg, by have := h.1 reg hreg; omega, hn⟩ hc
    · exact hs

/-- Exact HOL local `canonicalArith_reads_self_or_fresh` (`word_cseProof:2881-2910`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalArith_reads_self_or_fresh"
  (words_as_type_indexed_bitvec)]
theorem canonicalArith_reads_self_or_fresh {width : Nat} [NeZero width] (data : Knowledge)
    (a : Compiler.Encoders.Asm.HolArith width)
    (h : wfData width data ∧ canMemArith (canonicalArith data a) = true ∧
      sptLookup (firstRegOfArith a) data.toCanonical = none) :
    ∀ w ∈ arithReads (canonicalArith data a), sptLookup w data.toCanonical = none ∨
      sptLookup w data.toCanonical = some w := by
  obtain ⟨hw, hc, hd⟩ := h
  have sf := fun x => canonicalRegs_self_or_fresh_wf data x hw
  have sf' := fun x => canonicalRegs'_self_or_fresh_wf data (firstRegOfArith a) x ⟨hw, hd⟩
  have flip : ∀ y, (sptLookup y data.toCanonical = some y ∨ sptLookup y data.toCanonical = none) →
      sptLookup y data.toCanonical = none ∨ sptLookup y data.toCanonical = some y :=
    fun _ h => h.symm
  cases a with
  | binop op d r2 ri =>
    cases ri <;> simp only [canonicalArith, canonicalImmReg', arithReads, firstRegOfArith,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sf' ⊢
    · exact ⟨flip _ (sf' r2), flip _ (sf' _)⟩
    · exact flip _ (sf' r2)
  | shift op d r2 ri =>
    cases ri
    · simp [canonicalArith, canonicalImmReg', canMemArith] at hc
    · simp only [canonicalArith, canonicalImmReg', arithReads, firstRegOfArith,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq] at sf' ⊢
      exact flip _ (sf' r2)
  | div d r2 r3 =>
    simp only [canonicalArith, arithReads, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨flip _ (sf r2), flip _ (sf r3)⟩
  | _ => simp [canonicalArith, canMemArith] at hc

end Moves

section WordCse

/-- Exact HOL local `can_mem_arith_ODD_reads` (`word_cseProof:1511-1516`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "can_mem_arith_ODD_reads"
  (words_as_type_indexed_bitvec)]
theorem canMemArith_odd_reads {width : Nat} [NeZero width] (a : Compiler.Encoders.Asm.HolArith width)
    (h : canMemArith a = true) : ∀ w ∈ arithReads a, w % 2 = 1 := by
  cases a with
  | binop op d r1 ri =>
    cases ri <;> simp_all [canMemArith, arithReads]
  | shift op d r1 ri =>
    cases ri <;> simp_all [canMemArith, arithReads]
  | div d r1 r2 => simp_all [canMemArith, arithReads]
  | _ => simp [canMemArith] at h

/-- Invalidation leaves the written register untracked (Flapjack
    infrastructure). -/
theorem lookup_invalidateData_self (data : Knowledge) (r : Nat) :
    sptLookup r (invalidateData data r).toCanonical = none := by
  unfold invalidateData keepData
  split
  · rename_i h; simpa using h
  · rfl

/-- Invalidation keeps untracked registers untracked (Flapjack
    infrastructure). -/
theorem lookup_invalidateData_none (data : Knowledge) (r x : Nat)
    (h : sptLookup x data.toCanonical = none) :
    sptLookup x (invalidateData data r).toCanonical = none := by
  unfold invalidateData
  split
  · exact h
  · rfl

theorem lookup_invalidateRegs_none :
    ∀ (rs : List Nat) (data : Knowledge) (x : Nat), sptLookup x data.toCanonical = none →
      sptLookup x (invalidateRegs data rs).toCanonical = none
  | [], _, _, h => h
  | r :: rs, data, x, h =>
      lookup_invalidateRegs_none rs _ x (lookup_invalidateData_none data r x h)

theorem lookup_invalidateRegs_mem :
    ∀ (rs : List Nat) (data : Knowledge) (x : Nat), x ∈ rs →
      sptLookup x (invalidateRegs data rs).toCanonical = none
  | [], _, _, h => by simp at h
  | r :: rs, data, x, h => by
      simp only [invalidateRegs]
      rcases List.mem_cons.mp h with rfl | hm
      · exact lookup_invalidateRegs_none rs _ x (lookup_invalidateData_self data x)
      · exact lookup_invalidateRegs_mem rs _ x hm

theorem firstRegOfArith_mem_writes {width : Nat} [NeZero width]
    (a : Compiler.Encoders.Asm.HolArith width) : firstRegOfArith a ∈ arithWrites a := by
  cases a <;> simp [firstRegOfArith, arithWrites]

theorem wfData_invalidateRegs_loads {width : Nat} [NeZero width] (data : Knowledge) (rs : List Nat)
    (h : wfData width data) :
    wfData width { invalidateRegs data rs with loadsMem := Misc.BalancedMap.empty } :=
  wfData_loads_wipe _ (wfData_invalidate_regs rs data h)

/-- The fresh-destination miss case shared by the instruction fact producers:
    a fresh odd destination self-mapped and stored under `key` (Flapjack
    infrastructure). -/
theorem wfData_fresh_instrs {width : Nat} [NeZero width] (data : Knowledge) (r : Nat) (key : List Nat)
    (h : wfData width data) (hr : sptLookup r data.toCanonical = none) (odd : r % 2 = 1)
    (ha : ∀ a : Compiler.Encoders.Asm.HolArith width, instToNumList (.arith a) = key →
      inNamesSet a (sptInsert r r data.toCanonical) ∧ canMemArith a = true)
    (hb : ∀ op src, opCurrHeapToNumList op src = key →
      sptLookup src (sptInsert r r data.toCanonical) = some src) :
    wfData width
      { { data with toCanonical := sptInsert r r data.toCanonical } with
        instrsMem := Misc.BalancedMap.insert listCmp key r
          ({ data with toCanonical := sptInsert r r data.toCanonical } : Knowledge).instrsMem } :=
  wfData_insert_instrs_key _ key r
    (wfData_insert_to_canonical data r r ⟨h, hr, sptLookup_sptInsert_same _ _ _, odd, odd⟩)
    (sptLookup_sptInsert_same _ _ _) ha hb

/-- A canonical substitute that avoids the destination is never the
    destination (Flapjack infrastructure). -/
theorem canonicalRegs'_ne (data : Knowledge) (r a : Nat) (ha : a ≠ r) :
    canonicalRegs' r data a ≠ r := by
  unfold canonicalRegs'
  dsimp only
  split
  · exact ha
  · assumption

/-- The register a canonical substitute names is self-mapped after it is
    registered (Flapjack infrastructure). -/
theorem canonicalRegs'_registered {width : Nat} [NeZero width] (data : Knowledge) (r a : Nat)
    (h : wfData width data) (hr : sptLookup r data.toCanonical = none) (ha : a % 2 = 1) :
    sptLookup (canonicalRegs' r data a)
      (registerRead data (canonicalRegs' r data a)).toCanonical = some (canonicalRegs' r data a) := by
  rw [lookup_register_read]
  rcases canonicalRegs'_self_or_fresh_wf data r a ⟨h, hr⟩ with hs | hn
  · rw [if_neg (fun hc => by rw [hs] at hc; exact absurd hc.2.2 (by simp))]; exact hs
  · have hodd : canonicalRegs' r data a % 2 ≠ 0 := by
      unfold canonicalRegs' canonicalRegs at hn ⊢
      dsimp only at hn ⊢
      split
      · omega
      · rename_i hne
        cases hl : sptLookup a data.toCanonical with
        | none => simp only [Option.getD_none]; omega
        | some c =>
          simp only [hl, Option.getD_some] at hn hne ⊢
          rw [if_neg hne] at hn
          exact absurd (h.1 a c hl).1 (by rw [hn]; simp)
    rw [if_pos ⟨rfl, hodd, hn⟩]

set_option linter.unusedSimpArgs false in
/-- The instruction clauses of `word_cse` keep `wf_data` (the `Inst` case of
    HOL `word_cse_wf_data`; Flapjack decomposition of that proof). -/
theorem wfData_wordCseInst {width : Nat} [NeZero width] (data : Knowledge)
    (i : Compiler.Encoders.Asm.HolInst width) (h : wfData width data) :
    wfData width (wordCseInst data i).1 := by
  cases i with
  | skip => exact h
  | const r w =>
    simp only [wordCseInst]
    split
    · exact wfData_invalidate data r h
    · rename_i hev
      exact wf_add_to_data_const _ r w _ _
        ⟨wfData_invalidate data r h, lookup_invalidateData_self data r, hev, rfl⟩
  | arith a =>
    simp only [wordCseInst]
    split
    · rename_i hc
      obtain ⟨hcan, hnot⟩ := hc
      set d1 := invalidateRegs data (arithWrites a) with hd1
      have w1 : wfData width d1 := wfData_invalidate_regs _ data h
      have r1 : sptLookup (firstRegOfArith a) d1.toCanonical = none :=
        lookup_invalidateRegs_mem _ data _ (firstRegOfArith_mem_writes a)
      set rds := arithReads (canonicalArith d1 a)
      have w2 : wfData width (registerReads d1 rds) := wfData_register_reads rds d1 w1
      have r2 : sptLookup (firstRegOfArith a) (registerReads d1 rds).toCanonical = none := by
        rw [lookup_register_reads]; simp [hnot, r1]
      refine wf_add_to_data_aux _ _ _ _ _ _ ⟨w2, r2, rfl, fun hev => ?_⟩
      have odd : firstRegOfArith a % 2 = 1 := by omega
      have names : inNamesSet (canonicalArith d1 a) (registerReads d1 rds).toCanonical :=
        inNamesSet_register_reads _ d1 ⟨canMemArith_odd_reads _ hcan,
          canonicalArith_reads_self_or_fresh d1 a ⟨w1, hcan, r1⟩⟩
      refine wfData_fresh_instrs _ _ _ w2 r2 odd (fun a2 ha2 => ?_)
        (fun op src hk => by simp [instToNumList, opCurrHeapToNumList] at hk)
      simp only [instToNumList, List.cons.injEq, true_and] at ha2
      obtain ⟨hc2, hreads, -⟩ := arithKeysEq (C := Unit) (F := Unit) _ a2 ⟨hcan, ha2.symm⟩
      exact ⟨fun reg hreg => (inNamesSet_insert_self _ _ _ names) reg (hreads ▸ hreg), hc2⟩
    · exact wfData_invalidate_regs _ data h
  | mem op r ad =>
    cases ad with
    | addr a ofs =>
      simp only [wordCseInst]
      split
      · exact wfData_loads_wipe data h
      · split
        · exact wfData_invalidate data r h
        · rename_i hev
          simp only [not_or] at hev
          obtain ⟨hr, ha, har⟩ := hev
          set d1 := invalidateData data r
          have w1 : wfData width d1 := wfData_invalidate data r h
          have r1 : sptLookup r d1.toCanonical = none := lookup_invalidateData_self data r
          set a' := canonicalRegs' r d1 a
          have hne : a' ≠ r := canonicalRegs'_ne d1 r a har
          have w2 := wfData_register_read d1 a' w1
          have r2 : sptLookup r (registerRead d1 a').toCanonical = none := by
            rw [lookup_register_read, if_neg (fun hc => hne hc.1.symm), r1]
          have self2 : sptLookup a' (registerRead d1 a').toCanonical = some a' :=
            canonicalRegs'_registered d1 r a w1 r1 (by omega)
          refine wf_add_to_load_aux _ _ _ _ _ _ ⟨w2, r2, rfl, fun hev2 => ?_⟩
          have w3 := wfData_insert_to_canonical _ r r
            ⟨w2, r2, sptLookup_sptInsert_same _ _ _, by omega, by omega⟩
          exact wfData_insert_loads _ r op a' ofs
            ⟨w3, sptLookup_sptInsert_same _ _ _, self_insert_fresh r2 self2⟩
  | fp f => exact wfData_invalidate_regs _ data h

set_option linter.unusedSimpArgs false in
/-- Exact HOL `word_cse_wf_data` (`word_cseProof:2912-3302`), by structural
    recursion on the program as HOL's `Induct`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_wf_data"
  (words_as_type_indexed_bitvec)]
theorem word_cse_wf_data {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (data : Knowledge),
      wfData width data → wfData width (wordCse data p).1
  | .move r rs, data, h => by simp only [wordCse]; exact wf_canonicalMoveRegs data rs h
  | .inst i, data, h => by simp only [wordCse]; exact wfData_wordCseInst data _ h
  | .get r x, data, h => by
      simp only [wordCse, getClause]
      have w1 := wfData_invalidate data r h
      have r1 := lookup_invalidateData_self data r
      split
      · rename_i hn
        split
        · exact w1
        · rename_i hev
          exact wfData_insert_gets _ x r ⟨w1, r1, by omega, hn⟩
      · rename_i k hk
        split
        · exact w1
        · rename_i hev
          exact wfData_repoint _ r k w1 r1 (by omega) (w1.2.2.2.2.2.1 x k hk)
  | .set x e, data, h => by
      simp only [wordCse, setClause]
      split
      · exact wfData_empty
      · split
        · exact wfData_filter_gets data x h
        · rename_i v hv
          split
          · exact wfData_filter_gets data x h
          · rename_i hev
            have w1 := wfData_filter_gets data x h
            have w2 := wfData_reinsert_canonical _ v ⟨w1, by omega⟩
            have e : (sptLookup v data.toCanonical).getD v = lookupAny v data.toCanonical v := by
              unfold lookupAny; cases sptLookup v data.toCanonical <;> rfl
            dsimp only
            rw [e]
            refine wfData_cons_gets _ x (canonicalRegs data v) ⟨w2, ?_, ?_⟩
            · refine List.lookup_eq_none_iff.mpr (fun p hp => ?_)
              have := (List.mem_filter.mp hp).2
              simp only [decide_eq_true_eq] at this
              simpa [bne_iff_ne] using (Ne.symm this)
            · show sptLookup (canonicalRegs data v)
                (sptInsert v (lookupAny v data.toCanonical v) data.toCanonical) = _
              unfold canonicalRegs lookupAny
              cases hl : sptLookup v data.toCanonical with
              | none => simp [sptLookup_sptInsert_same]
              | some c =>
                simp only [Option.getD_some]
                by_cases hcv : c = v
                · subst hcv; exact sptLookup_sptInsert_same _ _ _
                · rw [sptLookup_sptInsert_ne _ _ _ _ hcv]; exact (h.1 v c hl).1
  | .mustTerminate p, data, h => by
      simp only [wordCse]; exact word_cse_wf_data p data h
  | .call _ _ _ _, _, _ => by simp only [wordCse]; exact wfData_empty
  | .seq p1 p2, data, h => by
      simp only [wordCse]
      exact word_cse_wf_data p2 _ (word_cse_wf_data p1 data h)
  | .ite _ _ _ p1 p2, data, h => by
      simp only [wordCse]
      exact wfData_merge _ _ ⟨word_cse_wf_data p1 data h, word_cse_wf_data p2 data h⟩
  | .opCurrHeap b r1 r2, data, h => by
      simp only [wordCse]
      split
      · exact wfData_invalidate data r1 h
      · rename_i hev
        simp only [not_or] at hev
        obtain ⟨hr2, hne2⟩ := hev
        set d1 := invalidateData data r1
        have w1 : wfData width d1 := wfData_invalidate data r1 h
        have r1n : sptLookup r1 d1.toCanonical = none := lookup_invalidateData_self data r1
        set a' := canonicalRegs' r1 d1 r2
        have hne : a' ≠ r1 := canonicalRegs'_ne d1 r1 r2 hne2
        have w2 := wfData_register_read d1 a' w1
        have r2n : sptLookup r1 (registerRead d1 a').toCanonical = none := by
          rw [lookup_register_read, if_neg (fun hc => hne hc.1.symm), r1n]
        have self2 : sptLookup a' (registerRead d1 a').toCanonical = some a' :=
          canonicalRegs'_registered d1 r1 r2 w1 r1n (by omega)
        refine wf_add_to_data_aux _ _ _ _ _ _ ⟨w2, r2n, rfl, fun hev2 => ?_⟩
        refine wfData_fresh_instrs _ _ _ w2 r2n (by omega)
          (fun a ha => by simp [instToNumList, opCurrHeapToNumList] at ha) (fun op src hk => ?_)
        simp only [opCurrHeapToNumList, List.cons.injEq, Nat.add_right_cancel_iff, and_true] at hk
        rw [hk.2.2]; exact self_insert_fresh r2n self2
  | .locValue r l, data, h => by
      simp only [wordCse]
      have w1 := wfData_invalidate data r h
      have r1 := lookup_invalidateData_self data r
      refine wf_add_to_data_aux _ _ _ _ _ _ ⟨w1, r1, rfl, fun hev => ?_⟩
      exact wfData_fresh_instrs _ _ _ w1 r1 (by omega)
        (fun a ha => by simp [instToNumList] at ha) (fun op src hk => by simp [opCurrHeapToNumList] at hk)
  | .skip, _, h => h
  | .store _ _, data, h => wfData_loads_wipe data h
  | .assign _ _, _, h => h
  | .raise _, _, h => h
  | .return _ _, _, h => h
  | .tick, _, h => h
  | .alloc _ _, _, _ => wfData_empty
  | .install _ _ _ _ _, _, _ => wfData_empty
  | .codeBufferWrite _ _, _, h => h
  | .dataBufferWrite _ _, _, h => h
  | .ffi _ _ _ _ _ _, _, _ => wfData_empty
  | .storeConsts r1 r2 r3 r4 _, data, h => by
      simp only [wordCse]; exact wfData_invalidateRegs_loads data _ h
  | .shareInst op r _, data, h => by
      simp only [wordCse]
      split
      · exact h
      · exact wfData_invalidate data r h
  | .loop _ _ _, _, _ => by simp only [wordCse]; exact wfData_empty
  | .break _, _, h => h
  | .continue _, _, h => h

end WordCse

end Flapjack.Compiler.Backend.WordCse
