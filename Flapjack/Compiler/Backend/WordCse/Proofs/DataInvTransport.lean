import Flapjack.Compiler.Backend.WordCse.Proofs.SemanticInvariant
import Flapjack.Compiler.Backend.WordCse.Proofs.CanonicalRegs
import Flapjack.Compiler.Backend.WordCse.Proofs.EvaluationFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.LoadEvaluation
import Flapjack.Compiler.Backend.WordCse.Proofs.DeletionFrames
import Flapjack.Compiler.Backend.WordCse.Proofs.WfDataPreservation
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateConst
import Flapjack.Compiler.Backend.WordInst.Proofs.ThreeToTwo

/-!
# `word_cseProof`: transport of the knowledge invariant

Counterpart of the `data_inv` transport lemmas of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (118-130, 160-165,
289-421, 507-575). An untracked register may be written or deleted, memory may
be replaced once the load facts are wiped, and a state that agrees on locals,
store and the memory fields satisfies the same invariant. The statements use
the reviewed `semInv`/`dataInv` over the faithful `WordSemStateFiniteExact`
and the accepted evaluation frames.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace DataInvTransportCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end DataInvTransportCarrier

/-- Exact HOL `data_inv_locals` (`word_cseProof:160-165`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_locals"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_locals {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) :
    ({ s with locals := s.locals } : WordSemStateFiniteExact width C F) = s := rfl

/-- Exact HOL `wf_data_untracked` (`word_cseProof:289-312`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_untracked"
  (words_as_type_indexed_bitvec)]
theorem wf_data_untracked {width : Nat} [NeZero width] (data : Knowledge) (n : Nat)
    (h : wfData width data ∧ sptLookup n data.toCanonical = none) :
    (∀ r v, sptLookup r data.toCanonical = some v → r ≠ n ∧ v ≠ n) ∧
    (∀ r v, sptLookup r data.toLatest = some v → r ≠ n ∧ v ≠ n) ∧
    (∀ k v, Misc.BalancedMap.lookup listCmp k data.instrsMem = some v → v ≠ n) ∧
    (∀ (a : HolArith width) v,
      Misc.BalancedMap.lookup listCmp (instToNumList (.arith a)) data.instrsMem = some v →
        n ∉ arithReads a ∧ canMemArith a = true) ∧
    (∀ op src v,
      Misc.BalancedMap.lookup listCmp (opCurrHeapToNumList op src) data.instrsMem = some v →
        src ≠ n) ∧
    (∀ x v, data.getsMem.lookup x = some v → v ≠ n) ∧
    (∀ k v, Misc.BalancedMap.lookup listCmp k data.loadsMem = some v → v ≠ n) ∧
    (∀ op a (ofs : BitVec width) v,
      Misc.BalancedMap.lookup listCmp (loadToNumList op a ofs) data.loadsMem = some v →
        a ≠ n) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, -, -, h9, h10, -⟩, hn⟩ := h
  have mapped : ∀ x w, sptLookup x data.toCanonical = some w → x ≠ n := by
    rintro x w hx rfl; rw [hn] at hx; cases hx
  have dom : ∀ x, sptDomain data.toCanonical x → x ≠ n := by
    rintro x hx rfl; simp [sptDomain, hn] at hx
  refine ⟨fun r v hr => ⟨mapped r v hr, mapped v v (h1 r v hr).1⟩,
    fun r v hr => ⟨dom r (h2 r v hr).1, dom v (h2 r v hr).2⟩,
    fun k v hk => mapped v v (h3 k v hk), fun a v hk => ?_,
    fun op src v hk => mapped src src (h5 op src v hk),
    fun x v hx => mapped v v (h6 x v hx), fun k v hk => mapped v v (h9 k v hk),
    fun op a ofs v hk => mapped a a (h10 op a ofs v hk)⟩
  obtain ⟨hnames, hc⟩ := h4 a v hk
  exact ⟨fun hmem => mapped n n (hnames n hmem) rfl, hc⟩

/-- `word_exp` of the `OpCurrHeap` key expression reads only the source
    register and the store (Flapjack infrastructure). -/
theorem wordExp_opCurrHeap_congr {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s t : WordSemStateFiniteExact width C F) (op : BinOp) (src : Nat)
    (hv : getVar src t = getVar src s) (hs : t.store = s.store) :
    wordExp t (.op op [.var src, .lookup .currHeap]) =
      wordExp s (.op op [.var src, .lookup .currHeap]) :=
  Compiler.Backend.WordInst.wordExp_op2_congr t s op _ _ _ _
    (by rw [wordExp, wordExp]; exact hv)
    (by rw [wordExp, wordExp]; simp only [getStore, hs])

/-- Generic transport of `sem_inv` to a state with the same store whose
    registers read by the invariant are unchanged and whose arithmetic and load
    equations transport (Flapjack decomposition of the HOL proofs). -/
theorem semInv_transport {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s t : WordSemStateFiniteExact width C F)
    (hw : wfData width data)
    (reg : ∀ x, sptDomain data.toCanonical x → getVar x t = getVar x s)
    (loc : ∀ x, sptLookup x data.toCanonical = some x → sptLookup x t.locals = sptLookup x s.locals)
    (store : t.store = s.store)
    (arith : ∀ (a : HolArith width) w, canMemArith a = true → inNamesSet a data.toCanonical →
      (evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s) →
        evaluate (.inst (.arith a.toWordLangArith)) t = (none, setVar (firstRegOfArith a) w t)))
    (load : ∀ op a (ofs : BitVec width) v r w, isStore op = false →
      Misc.BalancedMap.lookup listCmp (loadToNumList op a ofs) data.loadsMem = some v →
      sptLookup a data.toCanonical = some a →
      (evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) →
        evaluate (.inst (.mem op r (.addr a ofs))) t = (none, setVar r w t)))
    (h : semInv data s) : semInv data t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨w1, w2, w3, w4, w5, w6, -, -, w9, w10, -⟩ := hw
  have self : ∀ x, sptLookup x data.toCanonical = some x → sptDomain data.toCanonical x :=
    fun x hx => by simp [sptDomain, hx]
  have regSelf := fun x hx => reg x (self x hx)
  have locGet : ∀ x, sptLookup x data.toCanonical = some x → getVar x t = getVar x s :=
    regSelf
  refine ⟨fun r v hr => ?_, fun r v hr => ?_, fun d c v hk => ?_, fun a v hk => ?_,
    fun op src v hk => ?_, fun l v hk => ?_, fun x v hx => ?_, fun op a ofs v hk => ?_⟩
  · rw [reg r (by simp [sptDomain, hr]), reg v (self v (w1 r v hr).1)]; exact h1 r v hr
  · rw [reg r (w2 r v hr).1, reg v (w2 r v hr).2]; exact h2 r v hr
  · rw [loc v (w3 _ v hk)]; exact h3 d c v hk
  · obtain ⟨w, hg, he⟩ := h4 a v hk
    obtain ⟨hn, hc⟩ := w4 a v hk
    exact ⟨w, by rw [locGet v (w3 _ v hk)]; exact hg, arith a w hc hn he⟩
  · obtain ⟨w, he, hg⟩ := h5 op src v hk
    exact ⟨w, by rw [wordExp_opCurrHeap_congr s t op src (locGet src (w5 op src v hk)) store]; exact he,
      by rw [locGet v (w3 _ v hk)]; exact hg⟩
  · rw [loc v (w3 _ v hk)]; exact h6 l v hk
  · obtain ⟨w, hs, hg⟩ := h7 x v hx
    exact ⟨w, by rw [store]; exact hs, by rw [locGet v (w6 x v hx)]; exact hg⟩
  · obtain ⟨w, hg, he⟩ := h8 op a ofs v hk
    exact ⟨w, by rw [locGet v (w9 _ v hk.2)]; exact hg,
      fun r => load op a ofs v r w hk.1 hk.2 (w10 op a ofs v hk.2) (he r)⟩

/-- Exact HOL `data_inv_set_var` (`word_cseProof:314-339`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_set_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (n : Nat) (v : WordLocW width)
    (h : sptLookup n data.toCanonical = none) :
    (dataInv data (setVar n v s) ↔ dataInv data s) := by
  have ne : ∀ x, sptDomain data.toCanonical x → x ≠ n := by
    rintro x hx rfl; simp [sptDomain, h] at hx
  have gv : ∀ x, x ≠ n → getVar x (setVar n v s) = getVar x s := fun x hx => by
    simp only [getVar, setVar, sptLookup_sptInsert_ne _ _ _ _ hx]
  have nreads : ∀ (a : HolArith width), inNamesSet a data.toCanonical → n ∉ arithReads a :=
    fun a hn hm => ne n (by simp [sptDomain, hn n hm]) rfl
  constructor
  · rintro ⟨hw, hs⟩
    refine ⟨hw, semInv_transport data (setVar n v s) s hw (fun x hx => (gv x (ne x hx)).symm)
      (fun x hx => (gv x (ne x (by simp [sptDomain, hx]))).symm) rfl ?_ ?_ hs⟩
    · intro a w hc hn he
      exact (evaluateArithSetVar a n v w s ⟨hc, nreads a hn⟩).mp he
    · intro op a ofs _ r w hst _ ha he
      exact (evaluateLoadSetVar op r a ofs n v w s ⟨hst, ne a (by simp [sptDomain, ha])⟩).mp he
  · rintro ⟨hw, hs⟩
    refine ⟨hw, semInv_transport data s (setVar n v s) hw (fun x hx => gv x (ne x hx))
      (fun x hx => gv x (ne x (by simp [sptDomain, hx]))) rfl ?_ ?_ hs⟩
    · intro a w hc hn he
      exact (evaluateArithSetVar a n v w s ⟨hc, nreads a hn⟩).mpr he
    · intro op a ofs _ r w hst _ ha he
      exact (evaluateLoadSetVar op r a ofs n v w s ⟨hst, ne a (by simp [sptDomain, ha])⟩).mpr he

/-- Exact HOL `data_inv_unset_var` (`word_cseProof:402-421`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_unset_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_unset_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (n : Nat)
    (h : sptLookup n data.toCanonical = none) :
    (dataInv data (unsetVar n s) ↔ dataInv data s) := by
  have ne : ∀ x, sptDomain data.toCanonical x → x ≠ n := by
    rintro x hx rfl; simp [sptDomain, h] at hx
  have gv : ∀ x, x ≠ n → getVar x (unsetVar n s) = getVar x s := fun x hx => by
    simp only [getVar, unsetVar, sptLookup_sptDelete, hx, if_false]
  have nreads : ∀ (a : HolArith width), inNamesSet a data.toCanonical → n ∉ arithReads a :=
    fun a hn hm => ne n (by simp [sptDomain, hn n hm]) rfl
  constructor
  · rintro ⟨hw, hs⟩
    refine ⟨hw, semInv_transport data (unsetVar n s) s hw (fun x hx => (gv x (ne x hx)).symm)
      (fun x hx => (gv x (ne x (by simp [sptDomain, hx]))).symm) rfl ?_ ?_ hs⟩
    · intro a w hc hn he
      exact (evaluateArithUnsetVar a n w s ⟨hc, nreads a hn⟩).mp he
    · intro op a ofs _ r w hst _ ha he
      exact (evaluateLoadUnsetVar op r a ofs n w s ⟨hst, ne a (by simp [sptDomain, ha])⟩).mp he
  · rintro ⟨hw, hs⟩
    refine ⟨hw, semInv_transport data s (unsetVar n s) hw (fun x hx => gv x (ne x hx))
      (fun x hx => gv x (ne x (by simp [sptDomain, hx]))) rfl ?_ ?_ hs⟩
    · intro a w hc hn he
      exact (evaluateArithUnsetVar a n w s ⟨hc, nreads a hn⟩).mpr he
    · intro op a ofs _ r w hst _ ha he
      exact (evaluateLoadUnsetVar op r a ofs n w s ⟨hst, ne a (by simp [sptDomain, ha])⟩).mpr he

/-- Exact HOL `not_seen_data_inv_alist_insert` (`word_cseProof:423-433`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "not_seen_data_inv_alist_insert"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem not_seen_data_inv_alist_insert {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (l : Spt (WordLocW width)) (r : Nat)
    (v : WordLocW width) (h : sptLookup r data.toCanonical = none)
    (hl : dataInv data ({ s with locals := l } : WordSemStateFiniteExact width C F)) :
    dataInv data ({ s with locals := sptInsert r v l } : WordSemStateFiniteExact width C F) := by
  exact (data_inv_set_var data ({ s with locals := l } : WordSemStateFiniteExact width C F) r v h).mpr hl

/-- Exact HOL `data_inv_memory` (`word_cseProof:507-519`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_memory {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (h : dataInv data s) :
    dataInv { data with loadsMem := Misc.BalancedMap.empty }
      ({ s with memory := m } : WordSemStateFiniteExact width C F) := by
  obtain ⟨hw, hs⟩ := h
  have noLoad : ∀ k v, Misc.BalancedMap.lookup listCmp k
      ({ data with loadsMem := Misc.BalancedMap.empty } : Knowledge).loadsMem ≠ some v := by
    intro k v; simp [Misc.BalancedMap.empty, Misc.BalancedMap.lookup]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, -⟩ := hs
  have hs0 : semInv { data with loadsMem := Misc.BalancedMap.empty } s :=
    ⟨g1, g2, g3, g4, g5, g6, g7, fun op a ofs v hk => absurd hk.2 (noLoad _ v)⟩
  refine ⟨wfData_loads_wipe data hw, semInv_transport _ s _ (wfData_loads_wipe data hw)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl
    (fun a w hc _ he => (evaluateArithMemory a w s m hc).mpr he)
    (fun op a ofs v r w _ hk _ _ => absurd hk (noLoad _ v)) hs0⟩

/-- Exact HOL `data_inv_state_agree` (`word_cseProof:555-575`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_state_agree"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem data_inv_state_agree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s1 s2 : WordSemStateFiniteExact width C F)
    (h : dataInv data s1 ∧ s2.locals = s1.locals ∧ s2.store = s1.store ∧ s2.memory = s1.memory ∧
      s2.mdomain = s1.mdomain ∧ s2.be = s1.be) :
    dataInv data s2 := by
  obtain ⟨⟨hw, hs⟩, hl, hst, hm, hd, hb⟩ := h
  have gv : ∀ x, getVar x s2 = getVar x s1 := fun x => by simp only [getVar, hl]
  exact ⟨hw, semInv_transport data s1 s2 hw (fun x _ => gv x) (fun x _ => by rw [hl]) hst
    (fun a w hc _ he => evaluateArithAgree a w s1 s2 ⟨he, hc, hl⟩)
    (fun op a ofs _ r w hst' _ _ he => evaluateLoadAgree op r a ofs w s1 s2 ⟨he, hst', hl, hm, hd, hb⟩) hs⟩

set_option linter.unusedSimpArgs false in
/-- Exact HOL `canonicalArith_correct` (`word_cseProof:118-130`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalArith_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem canonicalArith_correct {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (s : WordSemStateFiniteExact width C F) (a : HolArith width)
    (h : dataInv data s) :
    inst (.arith (canonicalArith data a).toWordLangArith) s = inst (.arith a.toWordLangArith) s := by
  have hc : ∀ x, getVar (canonicalRegs data x) s = getVar x s :=
    fun x => canonicalRegsCorrect data x s h
  have hc' : ∀ d x, getVar (canonicalRegs' d data x) s = getVar x s :=
    fun d x => canonicalRegsAvoidCorrect d data x s h
  have hv : ∀ x y, getVar x s = getVar y s → wordExp s (.var x) = wordExp s (.var y) :=
    fun x y hxy => by rw [wordExp, wordExp]; exact hxy
  have hk : ∀ w : BitVec width, wordExp s (.const w) = wordExp s (.const w) := fun _ => rfl
  cases a with
  | binop op d r2 ri =>
    cases ri <;> simp only [canonicalArith, canonicalImmReg', HolRegImm.toWordRegImm,
      HolArith.toWordLangArith, inst, assign]
    · rw [Compiler.Backend.WordInst.wordExp_op2_congr s s op _ _ _ _ (hv _ _ (hc' d r2))
        (hv _ _ (hc' d _))]
    · rw [Compiler.Backend.WordInst.wordExp_op2_congr s s op _ _ _ _ (hv _ _ (hc' d r2)) (hk _)]
  | shift sh d r2 ri =>
    cases ri <;> simp only [canonicalArith, canonicalImmReg', HolRegImm.toWordRegImm,
      HolArith.toWordLangArith, inst, assign]
    · rw [Compiler.Backend.WordInst.wordExp_shift_congr s s sh _ _ _ _ (hv _ _ (hc' d r2))
        (hv _ _ (hc' d _))]
    · rw [Compiler.Backend.WordInst.wordExp_shift_congr s s sh _ _ _ _ (hv _ _ (hc' d r2)) (hk _)]
  | div d r2 r3 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc]
  | longMul d1 d2 r3 r4 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc]
  | longDiv d1 d2 r3 r4 r5 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc]
  | addCarry d r2 r3 r4 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc']
  | addOverflow d r2 r3 r4 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc']
  | subOverflow d r2 r3 r4 =>
    simp only [canonicalArith, HolArith.toWordLangArith, inst, WordSemStateFiniteExact.getVars, hc']

end Flapjack.Compiler.Backend.WordCse
