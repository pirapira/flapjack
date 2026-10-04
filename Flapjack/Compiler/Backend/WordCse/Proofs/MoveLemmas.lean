import Flapjack.Compiler.Backend.WordCse.Proofs.FactInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.MoveStoreConsts

/-!
# `word_cseProof`: parallel moves and clock updates

Counterpart of the move and clock lemmas of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (1953-2290): the
canonicalised move sources read the same values, `set_vars` reads back the
moved values, the parallel-move knowledge update `canonicalMoveRegs` keeps the
invariant after the move, and clock/termdep updates change no evaluation
equation or invariant.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace MoveLemmasCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end MoveLemmasCarrier

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem getVars_map_congr (s : WordSemStateFiniteExact width C F) (f : Nat → Nat)
    (h : ∀ n, getVar (f n) s = getVar n s) :
    ∀ ns : List Nat, WordSemStateFiniteExact.getVars (ns.map f) s =
      WordSemStateFiniteExact.getVars ns s
  | [] => rfl
  | n :: ns => by simp only [List.map_cons, WordSemStateFiniteExact.getVars, h, getVars_map_congr s f h ns]

theorem getVars_cons_some (s : WordSemStateFiniteExact width C F) (n : Nat) (ns : List Nat)
    (vs : List (WordLocW width)) (h : WordSemStateFiniteExact.getVars (n :: ns) s = some vs) :
    ∃ v vs', vs = v :: vs' ∧ getVar n s = some v ∧ WordSemStateFiniteExact.getVars ns s = some vs' := by
  simp only [WordSemStateFiniteExact.getVars] at h
  cases hn : getVar n s with
  | none => rw [hn] at h; cases h
  | some v =>
    rw [hn] at h
    cases hs : WordSemStateFiniteExact.getVars ns s with
    | none => rw [hs] at h; cases h
    | some vs' => rw [hs] at h; cases h; exact ⟨v, vs', rfl, rfl, rfl⟩

end Helpers

/-- Exact HOL local `MAP_FST_lemma` (`word_cseProof:1953-1957`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MAP_FST_lemma"]
theorem MAP_FST_lemma {α : Type} (data : Knowledge) (moves : List (α × Nat)) :
    (moves.map (fun p => (p.1, canonicalRegs data p.2))).map Prod.fst = moves.map Prod.fst := by
  simp [List.map_map, Function.comp_def]

/-- Exact HOL local `MAP_SND_lemma` (`word_cseProof:1959-1969`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MAP_SND_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem MAP_SND_lemma {width : Nat} [NeZero width] {C : Type} {F : Type} {α : Type}
    (s : WordSemStateFiniteExact width C F) (data : Knowledge) (moves : List (α × Nat))
    (x : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s = some x ∧ dataInv data s) :
    WordSemStateFiniteExact.getVars
      ((moves.map (fun p => (p.1, canonicalRegs data p.2))).map Prod.snd) s = some x := by
  have hm : (moves.map (fun p => (p.1, canonicalRegs data p.2))).map Prod.snd =
      (moves.map Prod.snd).map (canonicalRegs data) := by simp [List.map_map, Function.comp_def]
  rw [hm, getVars_map_congr s _ (fun n => canonicalRegsCorrect data n s h.2)]
  exact h.1

/-- Exact HOL `lookup_map_insert0` (`word_cseProof:1971-1981`); HOL `ALOOKUP l x`
    is `List.lookup x l`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_map_insert0"]
theorem lookup_map_insert0 {α : Type} (m : Spt α) (xs : List (Nat × α)) (r : Nat) :
    sptLookup r (mapInsert xs m) =
      match xs.lookup r with
      | none => sptLookup r m
      | some r' => some r' := by
  rw [sptLookup_mapInsert]
  cases xs.lookup r <;> rfl

/-- Exact HOL `get_set_vars_lemma` (`word_cseProof:1983-1994`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_set_vars_lemma {width : Nat} [NeZero width] {C : Type} {F : Type}
    (xs : List Nat) (xs' : List (WordLocW width)) (x y : Nat) (s : WordSemStateFiniteExact width C F)
    (h : x ∉ xs ∧ y ∉ xs) (hxy : getVar x s = getVar y s) :
    getVar x (setVars xs xs' s) = getVar y (setVars xs xs' s) := by
  simp only [getVar, setVars, WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ _ h.1,
    WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ _ h.2]
  exact hxy

/-- Exact HOL local `get_set_vars_not_in` (`word_cseProof:1996-2013`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_not_in"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_set_vars_not_in {width : Nat} [NeZero width] {C : Type} {F : Type}
    (rs : List Nat) (vs : List (WordLocW width)) (r : Nat) (s : WordSemStateFiniteExact width C F)
    (h : r ∉ rs) : getVar r (setVars rs vs s) = getVar r s := by
  simp only [getVar, setVars, WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ _ h]

/-- Exact HOL `MEM_FST_reduc` (`word_cseProof:2008-2013`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MEM_FST_reduc"]
theorem MEM_FST_reduc {α β : Type} (moves : List (α × β)) (r : α) (p_2 : β)
    (h : (r, p_2) ∈ moves) : r ∈ moves.map Prod.fst :=
  List.mem_map.mpr ⟨(r, p_2), h, rfl⟩

/-- Exact HOL local `get_set_vars_in` (`word_cseProof:2015-2032`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_in"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_set_vars_in {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (moves : List (Nat × Nat)) (r p_2 : Nat) (x : List (WordLocW width))
      (s : WordSemStateFiniteExact width C F),
      (r, p_2) ∈ moves → (moves.map Prod.fst).Nodup →
      WordSemStateFiniteExact.getVars (moves.map Prod.snd) s = some x →
      getVar r (setVars (moves.map Prod.fst) x s) = getVar p_2 s
  | [], _, _, _, _, hm, _, _ => by simp at hm
  | (a, b) :: ms, r, p_2, x, s, hm, hnd, hg => by
      obtain ⟨v, vs, rfl, hb, hms⟩ := getVars_cons_some s b _ x hg
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.map_cons, getVar, setVars, LoopSemStateFiniteExact.sptAlistInsert]
      rcases List.mem_cons.mp hm with he | hm'
      · cases he; rw [sptLookup_sptInsert_same]; exact hb.symm
      · have hra : r ≠ a := by
          rintro rfl; exact hnd.1 (MEM_FST_reduc ms r p_2 hm')
        rw [sptLookup_sptInsert_ne _ _ _ _ hra]
        exact get_set_vars_in ms r p_2 vs s hm' hnd.2 hms

/-- Exact HOL local `get_set_vars_in_2` (`word_cseProof:2034-2047`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_in_2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_set_vars_in_2 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (moves : List (Nat × Nat)) (r p_2 x' : Nat) (x : List (WordLocW width)) (data : Knowledge)
    (s : WordSemStateFiniteExact width C F)
    (hm : (r, p_2) ∈ moves) (hnd : (moves.map Prod.fst).Nodup)
    (hl : sptLookup p_2 data.toCanonical = some x')
    (hg : WordSemStateFiniteExact.getVars
      ((moves.map (fun p => (p.1, canonicalRegs data p.2))).map Prod.snd) s = some x) :
    getVar r (setVars (moves.map Prod.fst) x s) = getVar x' s := by
  have hm' : (r, canonicalRegs data p_2) ∈ moves.map (fun p => (p.1, canonicalRegs data p.2)) :=
    List.mem_map.mpr ⟨(r, p_2), hm, rfl⟩
  have := get_set_vars_in _ r _ x s hm' (by rw [MAP_FST_lemma]; exact hnd) hg
  rw [MAP_FST_lemma] at this
  rw [this]
  simp [canonicalRegs, hl]

/-- Exact HOL local `lookup_set_vars_not_in` (`word_cseProof:2049-2056`); the
    unused HOL binder `data` is retained. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_set_vars_not_in"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_set_vars_not_in {width : Nat} [NeZero width] {C : Type} {F : Type} {β : Type}
    (s : WordSemStateFiniteExact width C F) (moves : List (Nat × β)) (v : Nat) (_data : Knowledge)
    (c : BitVec width) (x : List (WordLocW width))
    (hv : v ∉ moves.map Prod.fst) (hl : sptLookup v s.locals = some (.word c)) :
    sptLookup v (setVars (moves.map Prod.fst) x s).locals = some (.word c) := by
  simp only [setVars, WordAlloc.sptLookup_sptAlistInsert_notMem _ _ _ _ hv]
  exact hl

/-- Exact HOL local `list_insert_insert` (`word_cseProof:2058-2064`), over the
    rendering `sptListInsert` of HOL sptree `list_insert`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "list_insert_insert"]
theorem list_insert_insert :
    ∀ (l : List Nat) (n : Nat) (an : NumSet),
      sptListInsert l (sptInsert n () an) = sptInsert n () (sptListInsert l an)
  | [], _, _ => rfl
  | k :: l, n, an => by
      simp only [sptListInsert]
      by_cases hk : k = n
      · subst hk; exact list_insert_insert l k (sptInsert k () an)
      · rw [sptInsert_swap k n () () an hk]
        exact list_insert_insert l n (sptInsert k () an)

/-- Exact HOL local `data_inv_insert_canonical_pair` (`word_cseProof:2066-2087`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_canonical_pair"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_canonical_pair {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x y : Nat) (tc tl : Spt Nat)
    (h : dataInv { data with toCanonical := tc, toLatest := tl } s ∧ sptLookup x tc = none ∧
      sptLookup y (sptInsert x y tc) = some y ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ getVar x s = getVar y s) :
    dataInv { data with toCanonical := sptInsert x y tc, toLatest := tl } s :=
  data_inv_insert_to_canonical { data with toCanonical := tc, toLatest := tl } s x y h

/-- Exact HOL local `data_inv_insert_pair` (`word_cseProof:2089-2106`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_pair"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_insert_pair {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (x y : Nat) (tc tl : Spt Nat)
    (h : dataInv { data with toCanonical := tc, toLatest := tl } s ∧ sptLookup x tc = none ∧
      sptLookup y tc = some y ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ getVar x s = getVar y s) :
    dataInv { data with toCanonical := sptInsert x y tc, toLatest := sptInsert y x tl } s := by
  obtain ⟨hd, hx, hy, ox, oy, hg⟩ := h
  have hy' := self_insert_fresh (y := y) hx hy
  have d1 := data_inv_insert_canonical_pair data s x y tc tl ⟨hd, hx, hy', ox, oy, hg⟩
  exact data_inv_insert_to_latest _ s y x
    ⟨d1, by simp [sptDomain, hy'], by simp [sptDomain, sptLookup_sptInsert_same], hg.symm⟩

/-- Exact HOL local `data_inv_move_pairs` (`word_cseProof:2108-2141`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_move_pairs"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_move_pairs {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (ps : List (Nat × Nat)) (data : Knowledge) (s : WordSemStateFiniteExact width C F),
      dataInv data s ∧ (ps.map Prod.fst).Nodup ∧
        (∀ p ∈ ps, sptLookup p.1 data.toCanonical = none ∧ sptLookup p.2 data.toCanonical = some p.2 ∧
          p.1 % 2 = 1 ∧ getVar p.1 s = getVar p.2 s) →
      dataInv
        { data with
          toCanonical := mapInsert ps data.toCanonical
          toLatest := mapInsert (ps.map (fun p => (p.2, p.1))) data.toLatest } s
  | [], _, _, h => h.1
  | (x, y) :: ps, data, s, h => by
      obtain ⟨hd, hnd, hps⟩ := h
      simp only [List.map_cons, List.nodup_cons] at hnd
      have ih := data_inv_move_pairs ps data s
        ⟨hd, hnd.2, fun p hp => hps p (List.mem_cons_of_mem _ hp)⟩
      obtain ⟨hx, hy, ox, hg⟩ := hps (x, y) List.mem_cons_self
      have notKey : ∀ v w, sptLookup v data.toCanonical = some w → ps.lookup v = none := by
        intro v w hv
        refine List.lookup_eq_none_iff.mpr (fun p hp => ?_)
        have := (hps p (List.mem_cons_of_mem _ hp)).1
        simp only [bne_iff_ne, ne_eq]
        rintro rfl; rw [this] at hv; cases hv
      have hx' : sptLookup x (mapInsert ps data.toCanonical) = none := by
        rw [sptLookup_mapInsert]
        have : ps.lookup x = none := List.lookup_eq_none_iff.mpr (fun p hp => by
          simp only [bne_iff_ne, ne_eq]
          rintro rfl; exact hnd.1 (List.mem_map.mpr ⟨p, hp, rfl⟩))
        rw [this]; exact hx
      have hy' : sptLookup y (mapInsert ps data.toCanonical) = some y := by
        rw [sptLookup_mapInsert, notKey y y hy]; exact hy
      exact data_inv_insert_pair data s x y _ _
        ⟨ih, hx', hy', ox, (hd.1.1 y y hy).2.2, hg⟩

/-- Exact HOL `canonicalMoveRegs_lemma` (`word_cseProof:2143-2234`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalMoveRegs_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalMoveRegs_lemma {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (rs : List (Nat × Nat))
    (vs : List (WordLocW width))
    (h : dataInv data s ∧ (rs.map Prod.fst).Nodup ∧
      WordSemStateFiniteExact.getVars (rs.map Prod.snd) s = some vs) :
    dataInv (canonicalMoveRegs data rs) (setVars (rs.map Prod.fst) vs s) := by
  obtain ⟨hd, hnd, hg⟩ := h
  unfold canonicalMoveRegs
  dsimp only
  split
  · rename_i hall
    set d1 := registerReads data (rs.map Prod.snd)
    have dd1 : dataInv d1 s := data_inv_register_reads _ data s hd
    have keys : ∀ x ∈ rs.map Prod.fst, sptLookup x d1.toCanonical = none := by
      intro x hx
      have := List.all_eq_true.mp hall x hx
      simpa [keepData] using this
    have ds' : dataInv d1 (setVars (rs.map Prod.fst) vs s) :=
      (data_inv_set_vars _ vs d1 s keys).mpr dd1
    refine data_inv_move_pairs _ d1 _ ⟨ds', ?_, fun p hp => ?_⟩
    · rw [List.map_map]
      exact (List.Sublist.map _ List.filter_sublist).nodup (by simpa [Function.comp_def] using hnd)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hqm, hodd⟩ := List.mem_filter.mp hq
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hodd
      have hk := keys q.1 (List.mem_map.mpr ⟨q, hqm, rfl⟩)
      have hsrc : ∃ c, sptLookup q.2 d1.toCanonical = some c := by
        rw [lookup_register_reads]
        split
        · exact ⟨_, rfl⟩
        · rename_i hc
          cases hl : sptLookup q.2 data.toCanonical with
          | some c => exact ⟨c, rfl⟩
          | none => exact absurd ⟨List.mem_map.mpr ⟨q, hqm, rfl⟩, hodd.2, hl⟩ hc
      obtain ⟨c, hc⟩ := hsrc
      have hcan : canonicalRegs d1 q.2 = c := by simp [canonicalRegs, hc]
      have hself := (dd1.1.1 q.2 c hc).1
      have hcnot : c ∉ rs.map Prod.fst := fun hm => by rw [keys c hm] at hself; cases hself
      refine ⟨hk, by simpa [hcan] using hself, by omega, ?_⟩
      simp only [hcan]
      rw [get_set_vars_in rs q.1 q.2 vs s hqm hnd hg, get_set_vars_not_in _ _ c s hcnot, ← hcan,
        canonicalRegsCorrect d1 q.2 s dd1]
  · exact dataInvEmpty _

/-- Exact HOL local `if_eq_rw` (`word_cseProof:2236-2239`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "if_eq_rw"]
theorem if_eq_rw {α : Type} [DecidableEq α] (x y : α) : (if x = y then y else x) = x := by
  split <;> simp_all

/-- Exact HOL local `evaluate_arith_clock` (`word_cseProof:2241-2253`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_arith_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F) (c td : Nat)
    (h : canMemArith a = true) :
    (evaluate (.inst (.arith a.toWordLangArith))
        ({ s with clock := c, termdep := td } : WordSemStateFiniteExact width C F) =
      (none, ({ setVar (firstRegOfArith a) w s with clock := c, termdep := td } :
        WordSemStateFiniteExact width C F)) ↔
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s)) :=
  ⟨fun he => evaluateArithAgree a w _ s ⟨he, h, rfl⟩,
    fun he => evaluateArithAgree a w s _ ⟨he, h, rfl⟩⟩

/-- Exact HOL local `evaluate_load_clock` (`word_cseProof:2255-2271`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (w : WordLocW width)
    (s : WordSemStateFiniteExact width C F) (c td : Nat) (h : ¬isStore op) :
    (evaluate (.inst (.mem op r (.addr a ofs)))
        ({ s with clock := c, termdep := td } : WordSemStateFiniteExact width C F) =
      (none, ({ setVar r w s with clock := c, termdep := td } : WordSemStateFiniteExact width C F)) ↔
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s)) := by
  have hs : isStore op = false := by simpa using h
  exact ⟨fun he => evaluateLoadAgree op r a ofs w _ s ⟨he, hs, rfl, rfl, rfl, rfl⟩,
    fun he => evaluateLoadAgree op r a ofs w s _ ⟨he, hs, rfl, rfl, rfl, rfl⟩⟩

/-- Exact HOL `data_inv_clock` (`word_cseProof:2273-2292`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (c td : Nat) (h : dataInv data s) :
    dataInv data ({ s with clock := c, termdep := td } : WordSemStateFiniteExact width C F) :=
  data_inv_state_agree data s _ ⟨h, rfl, rfl, rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.WordCse
