import Flapjack.Compiler.Backend.WordCse.Proofs.DataInvUpdates

/-!
# `word_cseProof`: correctness of the CSE fact producers

Counterpart of the fact-insertion group of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (1204-1950): storing a
verified instruction or load fact keeps the knowledge invariant, and each fact
producer (`add_to_data_aux`, `add_to_data_const`, the `LocValue`, `OpCurrHeap`
and arithmetic wrappers, `add_to_load_aux` and the load wrapper) emits a program
with the original instruction's effect while preserving the invariant in the
post-state.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace FactInsertCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FactInsertCarrier

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem setVar_inj (d : Nat) (v w : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    setVar d v s = setVar d w s ↔ v = w := by
  constructor
  · intro h
    have := congrArg (fun t => sptLookup d t.locals) h
    simpa [setVar, sptLookup_sptInsert_same] using this
  · rintro rfl; rfl

theorem getVar_setVar_same (r : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    getVar r (setVar r w s) = some w := by
  simp only [getVar, setVar, sptLookup_sptInsert_same]

theorem getVar_setVar_other (r x : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : x ≠ r) : getVar x (setVar r w s) = getVar x s := by
  simp only [getVar, setVar, sptLookup_sptInsert_ne _ _ _ _ h]

theorem evaluate_opCurrHeap_eq (b : BinOp) (dst src : Nat) (s : WordSemStateFiniteExact width C F) :
    evaluate (.opCurrHeap b dst src) s =
      match wordExp s (.op b [.var src, .lookup .currHeap]) with
      | none => (some .error, s)
      | some w => (none, setVar dst w s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.1 src s dst b

theorem evaluate_locValue_eq (r l : Nat) (s : WordSemStateFiniteExact width C F) :
    evaluate (.locValue r l) s =
      if sptMem l s.code then (none, setVar r (.loc l 0) s) else (some .error, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s r l

theorem evaluate_const_eq (r : Nat) (w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    evaluate (.inst (.const r w)) s = (none, setVar r (.word w) s) := by
  rw [Compiler.Backend.WordInst.evaluate_inst_eq]
  simp only [inst, assign]
  rw [wordExp]

theorem arithOpToNum_inj (a b : BinOp) (h : arithOpToNum a = arithOpToNum b) : a = b := by
  cases a <;> cases b <;> simp_all [arithOpToNum]

theorem memOpToNum_inj (a b : HolMemop) (h : memOpToNum a = memOpToNum b) : a = b := by
  cases a <;> cases b <;> simp_all [memOpToNum]

/-- Inserting a verified instruction fact keeps `sem_inv` (Flapjack
    decomposition of the HOL fact-insert proofs). -/
theorem semInv_insert_instrs (d : Knowledge) (s : WordSemStateFiniteExact width C F) (key : List Nat)
    (r : Nat) (hinv : Misc.BalancedMap.invariant listCmp d.instrsMem) (hs : semInv d s)
    (hc : ∀ n (c : BitVec width), instToNumList (.const n c) = key →
      sptLookup r s.locals = some (.word c))
    (ha : ∀ a : HolArith width, instToNumList (.arith a) = key →
      ∃ w, getVar r s = some w ∧
        evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s))
    (ho : ∀ op src, opCurrHeapToNumList op src = key →
      ∃ w, wordExp s (.op op [.var src, .lookup .currHeap]) = some w ∧ getVar r s = some w)
    (hl : ∀ l, [48, l] = key → sptLookup r s.locals = some (.loc l 0)) :
    semInv { d with instrsMem := Misc.BalancedMap.insert listCmp key r d.instrsMem } s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  have ins := fun k => (lookup_insert_listCmp k key r d.instrsMem hinv).2
  refine ⟨h1, h2, fun n c v hk => ?_, fun a v hk => ?_, fun op src v hk => ?_, fun l v hk => ?_,
    h7, h8⟩
  · rw [ins] at hk; split at hk
    · cases hk; exact hc n c (by assumption)
    · exact h3 n c v hk
  · rw [ins] at hk; split at hk
    · cases hk; exact ha a (by assumption)
    · exact h4 a v hk
  · rw [ins] at hk; split at hk
    · cases hk; exact ho op src (by assumption)
    · exact h5 op src v hk
  · rw [ins] at hk; split at hk
    · cases hk; exact hl l (by assumption)
    · exact h6 l v hk

/-- Inserting a verified load fact keeps `sem_inv` (Flapjack decomposition). -/
theorem semInv_insert_loads (d : Knowledge) (s : WordSemStateFiniteExact width C F) (key : List Nat)
    (r : Nat) (hinv : Misc.BalancedMap.invariant listCmp d.loadsMem) (hs : semInv d s)
    (hld : ∀ op a (ofs : BitVec width), loadToNumList op a ofs = key → isStore op = false →
      ∃ w, getVar r s = some w ∧
        ∀ r', evaluate (.inst (.mem op r' (.addr a ofs))) s = (none, setVar r' w s)) :
    semInv { d with loadsMem := Misc.BalancedMap.insert listCmp key r d.loadsMem } s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  have ins := fun k => (lookup_insert_listCmp k key r d.loadsMem hinv).2
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun op a ofs v hk => ?_⟩
  obtain ⟨hst, hk⟩ := hk
  rw [ins] at hk; split at hk
  · cases hk; exact hld op a ofs (by assumption) hst
  · exact h8 op a ofs v ⟨hst, hk⟩

/-- The register named by a `to_latest` lookup holds the same value
    (Flapjack infrastructure). -/
theorem getVar_latest (d : Knowledge) (s : WordSemStateFiniteExact width C F) (hs : semInv d s)
    (r' : Nat) : getVar ((sptLookup r' d.toLatest).getD r') s = getVar r' s := by
  cases hl : sptLookup r' d.toLatest with
  | none => rfl
  | some k => exact (hs.2.1 r' k hl).symm

/-- The hit case of the fact producers (Flapjack decomposition). -/
theorem data_inv_repoint (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r r' : Nat)
    (w : WordLocW width) (h : dataInv data s) (hr : sptLookup r data.toCanonical = none)
    (odd : r % 2 = 1) (hself : sptLookup r' data.toCanonical = some r')
    (hv : getVar r' s = some w) :
    dataInv { data with toCanonical := sptInsert r r' data.toCanonical,
                        toLatest := sptInsert r' r data.toLatest } (setVar r w s) := by
  have hne : r' ≠ r := by rintro rfl; rw [hr] at hself; cases hself
  have d0 := (data_inv_set_var data s r w hr).mpr h
  have odd' := (h.1.1 r' r' hself).2.2
  have d1 := data_inv_insert_to_canonical data (setVar r w s) r r'
    ⟨d0, hr, self_insert_fresh hr hself, odd, odd',
      by rw [getVar_setVar_same, getVar_setVar_other r r' w s hne, hv]⟩
  exact data_inv_insert_to_latest _ (setVar r w s) r' r
    ⟨d1, by simp [sptDomain, self_insert_fresh hr hself],
      by simp [sptDomain, sptLookup_sptInsert_same],
      by rw [getVar_setVar_same, getVar_setVar_other r r' w s hne, hv]⟩

/-- The fresh-self-map step shared by the miss cases (Flapjack
    decomposition). -/
theorem data_inv_fresh (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat)
    (w : WordLocW width) (h : dataInv data s) (hr : sptLookup r data.toCanonical = none)
    (odd : r % 2 = 1) :
    dataInv { data with toCanonical := sptInsert r r data.toCanonical } (setVar r w s) :=
  data_inv_insert_to_canonical data (setVar r w s) r r
    ⟨(data_inv_set_var data s r w hr).mpr h, hr, sptLookup_sptInsert_same _ _ _, odd, odd, rfl⟩

end Helpers

/-- Exact HOL local `data_inv_insert_instrs_Const` (`word_cseProof:1204-1250`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_Const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_instrs_Const {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r n : Nat) (w : BitVec width)
    (h : dataInv data s ∧ sptLookup r data.toCanonical = some r ∧ sptLookup r s.locals = some (.word w)) :
    dataInv { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (instToNumList (.const n w)) r data.instrsMem } s := by
  obtain ⟨⟨hw, hs⟩, hr, hl⟩ := h
  refine ⟨wfData_insert_instrs_Const data r n w ⟨hw, hr⟩,
    semInv_insert_instrs data s _ r hw.2.2.2.2.2.2.2.1 hs (fun n' c hk => ?_)
      (fun a hk => by simp [instToNumList] at hk)
      (fun op src hk => by simp [instToNumList, opCurrHeapToNumList] at hk)
      (fun l hk => by simp [instToNumList] at hk)⟩
  simp only [instToNumList, wordToNum, List.cons.injEq, true_and, and_true] at hk
  rw [BitVec.eq_of_toNat_eq hk]; exact hl

/-- Exact HOL local `data_inv_insert_instrs_Arith` (`word_cseProof:1252-1314`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_Arith"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_instrs_Arith {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (a : HolArith width)
    (w : WordLocW width)
    (h : dataInv data s ∧ sptLookup r data.toCanonical = some r ∧ canMemArith a = true ∧
      inNamesSet a data.toCanonical ∧ getVar r s = some w ∧
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s)) :
    dataInv { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (instToNumList (.arith a)) r data.instrsMem } s := by
  obtain ⟨⟨hw, hs⟩, hr, hc, hn, hg, he⟩ := h
  refine ⟨wfData_insert_instrs_Arith data r a ⟨hw, hr, hc, hn⟩,
    semInv_insert_instrs data s _ r hw.2.2.2.2.2.2.2.1 hs
      (fun n c hk => by simp [instToNumList] at hk) (fun a2 hk => ?_)
      (fun op src hk => by simp [instToNumList, opCurrHeapToNumList] at hk)
      (fun l hk => by simp [instToNumList] at hk)⟩
  simp only [instToNumList, List.cons.injEq, true_and] at hk
  exact ⟨w, hg, (arithKeysEq a a2 ⟨hc, hk.symm⟩).2.2 s w he⟩

/-- Exact HOL local `data_inv_insert_instrs_OpCurrHeap` (`word_cseProof:1316-1362`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_OpCurrHeap"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_instrs_OpCurrHeap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (op : BinOp) (src : Nat)
    (w : WordLocW width)
    (h : dataInv data s ∧ sptLookup r data.toCanonical = some r ∧
      sptLookup src data.toCanonical = some src ∧
      wordExp s (.op op [.var src, .lookup .currHeap]) = some w ∧ getVar r s = some w) :
    dataInv { data with instrsMem :=
      Misc.BalancedMap.insert listCmp (opCurrHeapToNumList op src) r data.instrsMem } s := by
  obtain ⟨⟨hw, hs⟩, hr, hsrc, he, hg⟩ := h
  refine ⟨wfData_insert_instrs_OpCurrHeap data r op src ⟨hw, hr, hsrc⟩,
    semInv_insert_instrs data s _ r hw.2.2.2.2.2.2.2.1 hs
      (fun n c hk => by simp [instToNumList, opCurrHeapToNumList] at hk)
      (fun a hk => by simp [instToNumList, opCurrHeapToNumList] at hk) (fun op2 src2 hk => ?_)
      (fun l hk => by simp [opCurrHeapToNumList] at hk)⟩
  simp only [opCurrHeapToNumList, List.cons.injEq, Nat.add_right_cancel_iff, true_and,
    and_true] at hk
  obtain ⟨hop, rfl⟩ := hk
  rw [arithOpToNum_inj _ _ hop]
  exact ⟨w, he, hg⟩

/-- Exact HOL local `data_inv_insert_instrs_LocValue` (`word_cseProof:1364-1414`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_LocValue"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_instrs_LocValue {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r l : Nat)
    (h : dataInv data s ∧ sptLookup r data.toCanonical = some r ∧
      sptLookup r s.locals = some (.loc l 0)) :
    dataInv { data with instrsMem := Misc.BalancedMap.insert listCmp [48, l] r data.instrsMem } s := by
  obtain ⟨⟨hw, hs⟩, hr, hl⟩ := h
  refine ⟨wfData_insert_instrs_LocValue data r l ⟨hw, hr⟩,
    semInv_insert_instrs data s _ r hw.2.2.2.2.2.2.2.1 hs
      (fun n c hk => by simp [instToNumList] at hk) (fun a hk => by simp [instToNumList] at hk)
      (fun op src hk => by simp [opCurrHeapToNumList] at hk) (fun l2 hk => ?_)⟩
  simp only [List.cons.injEq, true_and, and_true] at hk
  rw [hk]; exact hl

/-- Exact HOL `add_to_data_aux_correct` (`word_cseProof:1416-1477`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_aux_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_data_aux_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (i : List Nat)
    (p : WordLangProgHOL (BitVec width)) (w : WordLocW width) (data' : Knowledge)
    (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧
      addToDataAux data r i p = (data', p') ∧ evaluate p s = (none, setVar r w s) ∧
      (∀ v, Misc.BalancedMap.lookup listCmp i data.instrsMem = some v → getVar v s = some w) ∧
      (¬ r % 2 = 0 → dataInv
        { { data with toCanonical := sptInsert r r data.toCanonical } with
          instrsMem := Misc.BalancedMap.insert listCmp i r
            ({ data with toCanonical := sptInsert r r data.toCanonical } : Knowledge).instrsMem }
        (setVar r w s))) :
    evaluate p' s = (none, setVar r w s) ∧ dataInv data' (setVar r w s) := by
  obtain ⟨hd, hr, he, hp, hhit, hmiss⟩ := h
  unfold addToDataAux at he
  split at he
  · rename_i r' hl
    have hv := hhit r' hl
    have hmove : evaluate (.move 0 [(r, (sptLookup r' data.toLatest).getD r')]) s =
        (none, setVar r w s) :=
      evaluate_Move1 0 r _ w s (by rw [getVar_latest data s hd.2 r']; exact hv)
    split at he
    · cases he; exact ⟨hmove, (data_inv_set_var data s r w hr).mpr hd⟩
    · cases he
      exact ⟨hmove, data_inv_repoint data s r r' w hd hr (by omega) (hd.1.2.2.1 i r' hl) hv⟩
  · split at he
    · cases he; exact ⟨hp, (data_inv_set_var data s r w hr).mpr hd⟩
    · rename_i hev
      cases he
      refine ⟨hp, data_inv_insert_to_latest _ (setVar r w s) r r ⟨hmiss hev, ?_, ?_, rfl⟩⟩ <;>
        simp [sptDomain, sptLookup_sptInsert_same]

/-- Exact HOL local `canonicalRegs_self_or_fresh` (`word_cseProof:1479-1494`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_self_or_fresh"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalRegs_self_or_fresh {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x : Nat) (h : dataInv data s) :
    sptLookup (canonicalRegs data x) data.toCanonical = some (canonicalRegs data x) ∨
      sptLookup (canonicalRegs data x) data.toCanonical = none :=
  canonicalRegs_self_or_fresh_wf data x h.1

/-- Exact HOL local `canonicalRegs'_self_or_fresh` (`word_cseProof:1496-1509`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_self_or_fresh"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalRegs'_self_or_fresh {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r1 x : Nat)
    (h : dataInv data s ∧ sptLookup r1 data.toCanonical = none) :
    sptLookup (canonicalRegs' r1 data x) data.toCanonical = some (canonicalRegs' r1 data x) ∨
      sptLookup (canonicalRegs' r1 data x) data.toCanonical = none :=
  canonicalRegs'_self_or_fresh_wf data r1 x ⟨h.1.1, h.2⟩

/-- Exact HOL `add_to_data_const_correct` (`word_cseProof:1523-1574`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_const_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_data_const_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (w : BitVec width)
    (data' : Knowledge) (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧ ¬ r % 2 = 0 ∧
      addToDataConst data r w = (data', p')) :
    evaluate p' s = (none, setVar r (.word w) s) ∧ dataInv data' (setVar r (.word w) s) := by
  obtain ⟨hd, hr, hev, he⟩ := h
  unfold addToDataConst at he
  dsimp only at he
  split at he
  · rename_i r' hl
    cases he
    refine ⟨evaluate_const_eq r w s, data_inv_repoint data s r r' _ hd hr (by omega)
      (hd.1.2.2.1 _ r' hl) ?_⟩
    exact hd.2.2.2.1 r w r' hl
  · cases he
    refine ⟨evaluate_const_eq r w s, ?_⟩
    have d1 := data_inv_fresh data s r (.word w) hd hr (by omega)
    have d2 := data_inv_insert_instrs_Const _ (setVar r (.word w) s) r r w
      ⟨d1, sptLookup_sptInsert_same _ _ _, sptLookup_sptInsert_same _ _ _⟩
    exact data_inv_insert_to_latest _ _ r r ⟨d2, by simp [sptDomain, sptLookup_sptInsert_same],
      by simp [sptDomain, sptLookup_sptInsert_same], rfl⟩

/-- Exact HOL `add_to_data_LocValue_correct` (`word_cseProof:1591`); HOL
    `l ∈ domain s.code` is `sptMem l s.code`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_LocValue_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_data_LocValue_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r l : Nat) (data' : Knowledge)
    (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧ sptMem l s.code ∧
      addToDataAux data r [48, l] (.locValue r l) = (data', p')) :
    evaluate p' s = (none, setVar r (.loc l 0) s) ∧ dataInv data' (setVar r (.loc l 0) s) := by
  obtain ⟨hd, hr, hcode, he⟩ := h
  refine add_to_data_aux_correct data s r [48, l] (.locValue r l) (.loc l 0) data' p'
    ⟨hd, hr, he, by rw [evaluate_locValue_eq, if_pos hcode], fun v hv => hd.2.2.2.2.2.2.1 l v hv,
      fun hev => ?_⟩
  exact data_inv_insert_instrs_LocValue _ _ r l
    ⟨data_inv_fresh data s r _ hd hr (by omega), sptLookup_sptInsert_same _ _ _,
      sptLookup_sptInsert_same _ _ _⟩

/-- Exact HOL `add_to_data_OpCurrHeap_correct` (`word_cseProof:1626`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_OpCurrHeap_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_data_OpCurrHeap_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (b : BinOp) (r1 r2 r2' : Nat)
    (w : WordLocW width) (data' : Knowledge) (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r1 data.toCanonical = none ∧ r2' = canonicalRegs' r1 data r2 ∧
      ¬ r2 % 2 = 0 ∧ r2 ≠ r1 ∧ wordExp s (.op b [.var r2, .lookup .currHeap]) = some w ∧
      addToDataAux (registerRead data r2') r1 (opCurrHeapToNumList b r2') (.opCurrHeap b r1 r2) =
        (data', p')) :
    evaluate p' s = (none, setVar r1 w s) ∧ dataInv data' (setVar r1 w s) := by
  obtain ⟨hd, hr1, rfl, hodd, hne21, hexp, he⟩ := h
  set r2' := canonicalRegs' r1 data r2
  have hne : r2' ≠ r1 := canonicalRegs'_ne data r1 r2 hne21
  have dD := data_inv_register_read data s r2' hd
  have rD : sptLookup r1 (registerRead data r2').toCanonical = none := by
    rw [lookup_register_read, if_neg (fun hc => hne hc.1.symm), hr1]
  have g2 : getVar r2' s = getVar r2 s := canonicalRegsAvoidCorrect r1 data r2 s hd
  have exp' : wordExp s (.op b [.var r2', .lookup .currHeap]) = some w := by
    rw [← hexp]
    exact Compiler.Backend.WordInst.wordExp_op2_congr s s b _ _ _ _
      (by rw [wordExp, wordExp]; exact g2) rfl
  refine add_to_data_aux_correct _ s r1 _ (.opCurrHeap b r1 r2) w data' p'
    ⟨dD, rD, he, by rw [evaluate_opCurrHeap_eq, hexp], fun v hv => ?_, fun hev => ?_⟩
  · obtain ⟨w', he', hg'⟩ := dD.2.2.2.2.2.1 b r2' v hv
    rw [exp'] at he'; cases he'; exact hg'
  · have self2 := canonicalRegs'_registered data r1 r2 hd.1 hr1 (by omega)
    refine data_inv_insert_instrs_OpCurrHeap _ _ r1 b r2' w
      ⟨data_inv_fresh _ s r1 w dD rD (by omega), sptLookup_sptInsert_same _ _ _,
        self_insert_fresh rD self2, ?_, getVar_setVar_same r1 w s⟩
    rw [wordExp_opCurrHeap_congr s (setVar r1 w s) b r2' (getVar_setVar_other r1 r2' w s hne) rfl]
    exact exp'

/-- Exact HOL `add_to_data_Arith_correct` (`word_cseProof:1691`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_Arith_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_data_Arith_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (a a' : HolArith width) (r : Nat)
    (w : WordLocW width) (data' : Knowledge) (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧ a' = canonicalArith data a ∧
      canMemArith a' = true ∧ r ∉ arithReads a' ∧ r = firstRegOfArith a ∧
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar r w s) ∧
      addToData (registerReads data (arithReads a')) r (.arith a') (.arith a) = (data', p')) :
    evaluate p' s = (none, setVar r w s) ∧ dataInv data' (setVar r w s) := by
  obtain ⟨hd, hr, rfl, hcan, hnot, rfl, heval, he⟩ := h
  set a' := canonicalArith data a
  set D := registerReads data (arithReads a')
  have dD : dataInv D s := data_inv_register_reads _ data s hd
  have rD : sptLookup (firstRegOfArith a) D.toCanonical = none := by
    rw [lookup_register_reads]; simp [hnot, hr]
  have first : firstRegOfArith a' = firstRegOfArith a := firstRegOfArith_canonicalArith data a
  have eval' : evaluate (.inst (.arith a'.toWordLangArith)) s =
      (none, setVar (firstRegOfArith a) w s) := by
    rw [Compiler.Backend.WordInst.evaluate_inst_eq, canonicalArith_correct data s a hd,
      ← Compiler.Backend.WordInst.evaluate_inst_eq]
    exact heval
  unfold addToData at he
  refine add_to_data_aux_correct D s _ _ _ w data' p' ⟨dD, rD, he, heval, fun v hv => ?_,
    fun hev => ?_⟩
  · obtain ⟨w', hg', he'⟩ := dD.2.2.2.2.1 a' v hv
    rw [eval', first] at he'
    have := ((setVar_inj _ _ _ s).mp (Prod.mk.inj he').2.symm)
    rw [← this]; exact hg'
  · have names : inNamesSet a' D.toCanonical :=
      inNamesSet_register_reads _ data ⟨canMemArith_odd_reads _ hcan,
        canonicalArith_reads_self_or_fresh data a ⟨hd.1, hcan, hr⟩⟩
    refine data_inv_insert_instrs_Arith _ _ _ a' w
      ⟨data_inv_fresh _ s _ w dD rD (by omega), sptLookup_sptInsert_same _ _ _, hcan,
        inNamesSet_insert_self _ _ _ names, getVar_setVar_same _ w s, ?_⟩
    rw [first]
    have := (evaluateArithSetVar a' (firstRegOfArith a) w w s ⟨hcan, hnot⟩).mpr (first ▸ eval')
    rw [first] at this
    exact this

/-- Exact HOL local `data_inv_insert_loads` (`word_cseProof:1785`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_loads"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_loads {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (op : HolMemop) (a : Nat)
    (ofs : BitVec width) (w : WordLocW width)
    (h : dataInv data s ∧ sptLookup r data.toCanonical = some r ∧
      sptLookup a data.toCanonical = some a ∧ ¬isStore op ∧ getVar r s = some w ∧
      ∀ r', evaluate (.inst (.mem op r' (.addr a ofs))) s = (none, setVar r' w s)) :
    dataInv { data with loadsMem :=
      Misc.BalancedMap.insert listCmp (loadToNumList op a ofs) r data.loadsMem } s := by
  obtain ⟨⟨hw, hs⟩, hr, ha, -, hg, he⟩ := h
  refine ⟨wfData_insert_loads data r op a ofs ⟨hw, hr, ha⟩,
    semInv_insert_loads data s _ r hw.2.2.2.2.2.2.2.2.2.2 hs (fun op2 a2 ofs2 hk _ => ?_)⟩
  simp only [loadToNumList, wordToNum, List.cons.injEq, Nat.add_right_cancel_iff, and_true] at hk
  obtain ⟨hop, rfl, hofs⟩ := hk
  rw [memOpToNum_inj _ _ hop, BitVec.eq_of_toNat_eq hofs]
  exact ⟨w, hg, he⟩

/-- Exact HOL `add_to_load_aux_correct` (`word_cseProof:1816`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_load_aux_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_load_aux_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (r : Nat) (i : List Nat)
    (p : WordLangProgHOL (BitVec width)) (w : WordLocW width) (data' : Knowledge)
    (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧
      addToLoadAux data r i p = (data', p') ∧ evaluate p s = (none, setVar r w s) ∧
      (∀ v, Misc.BalancedMap.lookup listCmp i data.loadsMem = some v → getVar v s = some w) ∧
      (¬ r % 2 = 0 → dataInv
        { { data with toCanonical := sptInsert r r data.toCanonical } with
          loadsMem := Misc.BalancedMap.insert listCmp i r
            ({ data with toCanonical := sptInsert r r data.toCanonical } : Knowledge).loadsMem }
        (setVar r w s))) :
    evaluate p' s = (none, setVar r w s) ∧ dataInv data' (setVar r w s) := by
  obtain ⟨hd, hr, he, hp, hhit, hmiss⟩ := h
  unfold addToLoadAux at he
  split at he
  · rename_i r' hl
    have hv := hhit r' hl
    have hmove : evaluate (.move 0 [(r, (sptLookup r' data.toLatest).getD r')]) s =
        (none, setVar r w s) :=
      evaluate_Move1 0 r _ w s (by rw [getVar_latest data s hd.2 r']; exact hv)
    split at he
    · cases he; exact ⟨hmove, (data_inv_set_var data s r w hr).mpr hd⟩
    · cases he
      exact ⟨hmove, data_inv_repoint data s r r' w hd hr (by omega)
        (hd.1.2.2.2.2.2.2.2.2.1 i r' hl) hv⟩
  · split at he
    · cases he; exact ⟨hp, (data_inv_set_var data s r w hr).mpr hd⟩
    · rename_i hev
      cases he
      refine ⟨hp, data_inv_insert_to_latest _ (setVar r w s) r r ⟨hmiss hev, ?_, ?_, rfl⟩⟩ <;>
        simp [sptDomain, sptLookup_sptInsert_same]

/-- Exact HOL `add_to_load_correct` (`word_cseProof:1879`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_load_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem add_to_load_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (op : HolMemop) (r a a' : Nat)
    (ofs : BitVec width) (w : WordLocW width) (data' : Knowledge) (p' : WordLangProgHOL (BitVec width))
    (h : dataInv data s ∧ sptLookup r data.toCanonical = none ∧ a' = canonicalRegs' r data a ∧
      ¬isStore op ∧ ¬ r % 2 = 0 ∧ ¬ a % 2 = 0 ∧ a ≠ r ∧
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) ∧
      addToLoadAux (registerRead data a') r (loadToNumList op a' ofs)
        (.inst (.mem op r (.addr a ofs))) = (data', p')) :
    evaluate p' s = (none, setVar r w s) ∧ dataInv data' (setVar r w s) := by
  obtain ⟨hd, hr, rfl, hst, hodd, haodd, hne, heval, he⟩ := h
  have hst' : isStore op = false := by simpa using hst
  set a' := canonicalRegs' r data a
  have hne' : a' ≠ r := canonicalRegs'_ne data r a hne
  have dD := data_inv_register_read data s a' hd
  have rD : sptLookup r (registerRead data a').toCanonical = none := by
    rw [lookup_register_read, if_neg (fun hc => hne' hc.1.symm), hr]
  have loc : sptLookup a s.locals = sptLookup a' s.locals := by
    have := canonicalRegsAvoidCorrect r data a s hd
    simp only [getVar] at this; exact this.symm
  have anyDest : ∀ r', evaluate (.inst (.mem op r' (.addr a' ofs))) s = (none, setVar r' w s) :=
    fun r' => evaluateLoadChangeAddr op r' a a' ofs w s
      ⟨hst', loc.symm, evaluateLoadAnyDest op r a ofs w s r' ⟨hst', heval⟩⟩
  refine add_to_load_aux_correct _ s r _ _ w data' p' ⟨dD, rD, he, heval, fun v hv => ?_,
    fun hev => ?_⟩
  · obtain ⟨w', hg', he'⟩ := dD.2.2.2.2.2.2.2.2 op a' ofs v ⟨hst', hv⟩
    have := (Prod.mk.inj ((he' r).symm.trans (anyDest r))).2
    rw [(setVar_inj _ _ _ s).mp this] at hg'; exact hg'
  · have self2 := canonicalRegs'_registered data r a hd.1 hr (by omega)
    refine data_inv_insert_loads _ _ r op a' ofs w
      ⟨data_inv_fresh _ s r w dD rD (by omega), sptLookup_sptInsert_same _ _ _,
        self_insert_fresh rD self2, hst, getVar_setVar_same r w s, fun r' => ?_⟩
    exact (evaluateLoadSetVar op r' a' ofs r w w s ⟨hst', hne'⟩).mpr (anyDest r')

end Flapjack.Compiler.Backend.WordCse
