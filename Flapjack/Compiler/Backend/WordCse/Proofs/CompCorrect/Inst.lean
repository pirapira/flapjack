import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect.Simple

/-!
# `word_cseProof` `comp_correct`: the instruction case

The `Inst` case of HOL `comp_correct` (`word_cseProof:3357-3484`), with HOL's
five instruction sub-cases (`Skip`, `Const`, `Arith`, `Mem`, `FP`). The helper
lemmas record which registers each successful instruction writes, so that the
invariant transports along invalidated knowledge.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact Compiler.Encoders.Asm

namespace CompCorrectInstCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompCorrectInstCarrier

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- A successful arithmetic instruction writes only its `arithWrites`
    registers, so it keeps an invariant that tracks none of them (Flapjack
    decomposition of the HOL `Inst` case). -/
theorem data_inv_inst_arith (d : Knowledge) (a : HolArith width)
    (s s' : WordSemStateFiniteExact width C F) (hd : dataInv d s)
    (hw : ∀ x ∈ arithWrites a, sptLookup x d.toCanonical = none)
    (h : inst (.arith a.toWordLangArith) s = some s') : dataInv d s' := by
  have sv : ∀ x v (t : WordSemStateFiniteExact width C F), x ∈ arithWrites a → dataInv d t →
      dataInv d (setVar x v t) := fun x v t hx ht => (data_inv_set_var d t x v (hw x hx)).mpr ht
  cases a <;> simp only [HolArith.toWordLangArith, inst, assign] at h <;> (repeat' split at h)
  all_goals first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h
       repeat (first | exact hd | apply sv _ _ _ (by simp [arithWrites])))

/-- A successful FP instruction writes only its `fpWrites` registers and FP
    registers (Flapjack decomposition of the HOL `Inst` case). -/
theorem data_inv_inst_fp (d : Knowledge) (f : HolFp) (s s' : WordSemStateFiniteExact width C F)
    (hd : dataInv d s) (hw : ∀ x ∈ fpWrites f, sptLookup x d.toCanonical = none)
    (h : inst (.fp f) s = some s') : dataInv d s' := by
  have sv : ∀ x v (t : WordSemStateFiniteExact width C F), x ∈ fpWrites f → dataInv d t →
      dataInv d (setVar x v t) := fun x v t hx ht => (data_inv_set_var d t x v (hw x hx)).mpr ht
  have sf : ∀ x v (t : WordSemStateFiniteExact width C F), dataInv d t → dataInv d (setFpVar x v t) :=
    fun x v t ht => (data_inv_set_fp_var d x v t).mpr ht
  cases f <;> simp only [inst] at h <;> (repeat' split at h)
  all_goals first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h
       repeat (first | exact hd | apply sf | apply sv _ _ _ (by simp [fpWrites])))

/-- The CSE-storable arithmetic shapes write exactly their first register. -/
theorem inst_arith_single (a : HolArith width) (s s' : WordSemStateFiniteExact width C F)
    (hshape : arithWrites a = [firstRegOfArith a]) (h : inst (.arith a.toWordLangArith) s = some s') :
    ∃ w, s' = setVar (firstRegOfArith a) w s := by
  cases a <;> simp [arithWrites, firstRegOfArith] at hshape
  all_goals
    simp only [HolArith.toWordLangArith, inst, assign, firstRegOfArith] at h ⊢
    repeat' split at h
  all_goals first
    | (simp at h; done)
    | exact ⟨_, (Option.some.inj h).symm⟩

/-- A successful load writes exactly its destination. -/
theorem inst_load_single (op : HolMemop) (r a : Nat) (ofs : BitVec width)
    (s s' : WordSemStateFiniteExact width C F) (hst : isStore op = false)
    (h : inst (.mem op r (.addr a ofs)) s = some s') : ∃ w, s' = setVar r w s := by
  cases op <;> simp only [isStore, Bool.true_eq_false] at hst <;> simp only [inst] at h <;>
    (repeat' split at h)
  all_goals first
    | (simp at h; done)
    | exact ⟨_, (Option.some.inj h).symm⟩

/-- A successful store changes only the memory. -/
theorem inst_store_memory (op : HolMemop) (r a : Nat) (ofs : BitVec width)
    (s s' : WordSemStateFiniteExact width C F) (hst : isStore op = true)
    (h : inst (.mem op r (.addr a ofs)) s = some s') :
    ∃ m, s' = ({ s with memory := m } : WordSemStateFiniteExact width C F) := by
  cases op <;> simp only [isStore, Bool.false_eq_true] at hst <;> simp only [inst] at h <;>
    (repeat' split at h)
  all_goals first
    | (simp at h; done)
    | exact ⟨_, (Option.some.inj h).symm⟩
    | (rename_i hm
       unfold memStore at hm
       split at hm
       · obtain rfl := Option.some.inj hm
         obtain rfl := Option.some.inj h
         exact ⟨_, rfl⟩
       · simp at hm)

end Helpers

/-- HOL `comp_correct`, `Inst` case (`word_cseProof:3357-3484`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem comp_correct_Inst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    CompCorrectAt (.inst i) s := by
  rintro res s' data p' data' ⟨he, -, hd, hres, hw⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = HolInst.toWordLangInst j := ⟨_, (HolInst.to_of i).symm⟩
  simp only [wordCse, HolInst.of_to] at hw
  rw [evaluate] at he
  split at he
  · rename_i s1 hs1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have orig : evaluate (.inst j.toWordLangInst) s = (none, s1) := by rw [evaluate, hs1]
    cases j with
    | skip =>
      simp only [wordCseInst] at hw
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
      simp only [HolInst.toWordLangInst, inst] at hs1
      cases hs1
      exact ⟨orig, fun _ => hd⟩
    | const r w =>
      simp only [wordCseInst] at hw
      have hs1' : s1 = setVar r (.word w) s := by
        simp only [HolInst.toWordLangInst, inst, assign] at hs1
        rw [wordExp] at hs1
        exact (Option.some.inj hs1).symm
      subst hs1'
      have dD := data_inv_invalidate data s r hd
      have rD := lookup_invalidateData_self data r
      split at hw
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨orig, fun _ => (data_inv_set_var _ s r _ rD).mpr dD⟩
      · rename_i hev
        obtain ⟨e1, i1⟩ := add_to_data_const_correct _ s r w data' p' ⟨dD, rD, hev, hw⟩
        exact ⟨e1, fun _ => i1⟩
    | arith a =>
      simp only [wordCseInst] at hw
      have dD : dataInv (invalidateRegs data (arithWrites a)) s :=
        data_inv_invalidate_regs _ data s hd
      have rD : sptLookup (firstRegOfArith a) (invalidateRegs data (arithWrites a)).toCanonical = none :=
        lookup_invalidate_regs _ data _ (firstRegOfArith_mem_writes a)
      split at hw
      · rename_i hgate
        obtain ⟨hcan, hnot⟩ := hgate
        have hshape : arithWrites a = [firstRegOfArith a] := by
          cases a <;> simp_all [canonicalArith, canMemArith, arithWrites, firstRegOfArith]
        obtain ⟨w, rfl⟩ := inst_arith_single a s s1 hshape hs1
        obtain ⟨e1, i1⟩ := add_to_data_Arith_correct _ s a _ _ w data' p'
          ⟨dD, rD, rfl, hcan, hnot, rfl, orig, hw⟩
        exact ⟨e1, fun _ => i1⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
        exact ⟨orig, fun _ => data_inv_inst_arith _ a s s1 dD
          (fun x hx => lookup_invalidate_regs _ data x hx) hs1⟩
    | mem op r ad =>
      cases ad with
      | addr a ofs =>
        simp only [wordCseInst] at hw
        split at hw
        · rename_i hst
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
          obtain ⟨m, rfl⟩ := inst_store_memory op r a ofs s s1 hst hs1
          exact ⟨orig, fun _ => data_inv_memory data s m hd⟩
        · rename_i hst
          have hst' : isStore op = false := by simpa using hst
          obtain ⟨w, rfl⟩ := inst_load_single op r a ofs s s1 hst' hs1
          have dD := data_inv_invalidate data s r hd
          have rD := lookup_invalidateData_self data r
          split at hw
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
            exact ⟨orig, fun _ => (data_inv_set_var _ s r w rD).mpr dD⟩
          · rename_i hguard
            simp only [not_or] at hguard
            obtain ⟨e1, i1⟩ := add_to_load_correct _ s op r a _ ofs w data' p'
              ⟨dD, rD, rfl, hst, hguard.1, hguard.2.1, hguard.2.2, orig, hw⟩
            exact ⟨e1, fun _ => i1⟩
    | fp f =>
      simp only [wordCseInst] at hw
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
      exact ⟨orig, fun _ => data_inv_inst_fp _ f s s1 (data_inv_invalidate_regs _ data s hd)
        (fun x hx => lookup_invalidate_regs _ data x hx) hs1⟩
  · cases he; exact absurd rfl hres

end Flapjack.Compiler.Backend.WordCse
