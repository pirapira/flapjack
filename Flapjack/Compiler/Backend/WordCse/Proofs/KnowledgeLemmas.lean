import Flapjack.Compiler.Backend.WordCse.CanonicalArith
import Flapjack.Compiler.Backend.WordCse.RegisterData
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Misc.BalancedMap.InsertCorrect
import Flapjack.Misc.BalancedMap.LookupSemantics

/-! `word_cseProof` knowledge lemmas that need no `wf_data`: the arithmetic
destination, the empty and inserted `listCmp` balanced maps, and the
`register_read(s)` field and `to_canonical` lookup equations. HOL's `¬EVEN r`
is rendered `r % 2 ≠ 0`, as in the reviewed `registerRead`. -/
namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Misc.BalancedMap Compiler.Encoders.Asm

/-- Exact HOL `firstRegOfArith_canonicalArith` (`word_cseProof:152-156`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "firstRegOfArith_canonicalArith"
  (words_as_type_indexed_bitvec)]
theorem firstRegOfArith_canonicalArith {width : Nat} [NeZero width]
    (data : Knowledge) (a : HolArith width) :
    firstRegOfArith (canonicalArith data a) = firstRegOfArith a := by
  cases a <;> rfl

/-- Exact HOL `lookup_listCmp_empty` (`word_cseProof:486-490`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_listCmp_empty"]
theorem lookup_listCmp_empty {α : Type} (k : List Nat) :
    lookup listCmp k (empty : Map (List Nat) α) = none := rfl

/-- Exact HOL `invariant_listCmp_empty` (`word_cseProof:498-502`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "invariant_listCmp_empty"]
theorem invariant_listCmp_empty {α : Type} :
    invariant listCmp (empty : Map (List Nat) α) := by
  simp [empty, invariant]

/-- Exact HOL `lookup_insert_listCmp` (`word_cseProof:775-787`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_insert_listCmp"]
theorem lookup_insert_listCmp {α : Type} (k i : List Nat) (v : α) (m : Map (List Nat) α)
    (h : invariant listCmp m) :
    invariant listCmp (insert listCmp i v m) ∧
    lookup listCmp k (insert listCmp i v m) = (if k = i then some v else lookup listCmp k m) := by
  classical
  have ins := insertThm listCmp i v m ⟨goodCmpListCmp, h⟩
  refine ⟨ins.1, ?_⟩
  rw [lookupThm listCmp k _ ⟨goodCmpListCmp, ins.1⟩, ins.2, lookupThm listCmp k m ⟨goodCmpListCmp, h⟩]
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have hkey : keySet listCmp k = keySet listCmp i ↔ k = i :=
    (keySetEq listCmp k i goodCmpListCmp).trans (listCmpEqCorrect k i)
  by_cases hki : k = i
  · simp [hki]
  · simp [hki, hkey.not.mpr hki]

/-- Exact HOL `register_read_simps` (`word_cseProof:789-796`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "register_read_simps"]
theorem register_read_simps (data : Knowledge) (r : Nat) :
    (registerRead data r).instrsMem = data.instrsMem ∧
    (registerRead data r).toLatest = data.toLatest ∧
    (registerRead data r).getsMem = data.getsMem ∧
    (registerRead data r).loadsMem = data.loadsMem := by
  unfold registerRead; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact HOL `register_reads_simps` (`word_cseProof:798-806`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "register_reads_simps"]
theorem register_reads_simps : ∀ (rs : List Nat) (data : Knowledge),
    (registerReads data rs).instrsMem = data.instrsMem ∧
    (registerReads data rs).toLatest = data.toLatest ∧
    (registerReads data rs).getsMem = data.getsMem ∧
    (registerReads data rs).loadsMem = data.loadsMem
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | r :: rs, data => by
      have ih := register_reads_simps rs (registerRead data r)
      have h1 := register_read_simps data r
      simp only [registerReads]
      exact ⟨ih.1.trans h1.1, ih.2.1.trans h1.2.1, ih.2.2.1.trans h1.2.2.1, ih.2.2.2.trans h1.2.2.2⟩

set_option linter.unusedSimpArgs false in
/-- Exact HOL `lookup_register_read` (`word_cseProof:808-814`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_register_read"]
theorem lookup_register_read (x : Nat) (data : Knowledge) (r : Nat) :
    sptLookup x (registerRead data r).toCanonical =
      if x = r ∧ r % 2 ≠ 0 ∧ sptLookup r data.toCanonical = none then some r
      else sptLookup x data.toCanonical := by
  unfold registerRead keepData
  by_cases hx : x = r
  · subst hx
    by_cases hr : x % 2 = 1 <;> by_cases hn : sptLookup x data.toCanonical = none <;>
      simp [Nat.mod_two_ne_zero, hr, hn, sptLookup_sptInsert_same]
  · split <;> simp [hx, sptLookup_sptInsert_ne _ _ _ _ hx]

set_option linter.unusedSimpArgs false in
/-- Exact HOL `lookup_register_reads` (`word_cseProof:816-824`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_register_reads"]
theorem lookup_register_reads : ∀ (rs : List Nat) (data : Knowledge) (x : Nat),
    sptLookup x (registerReads data rs).toCanonical =
      if x ∈ rs ∧ x % 2 ≠ 0 ∧ sptLookup x data.toCanonical = none then some x
      else sptLookup x data.toCanonical
  | [], _, x => by simp [registerReads]
  | r :: rs, data, x => by
      simp only [registerReads]
      rw [lookup_register_reads rs (registerRead data r) x, lookup_register_read x data r]
      by_cases hx : x = r
      · subst hx
        by_cases hr : x % 2 = 1 <;> by_cases hn : sptLookup x data.toCanonical = none <;>
          simp [Nat.mod_two_ne_zero, hr, hn]
      · by_cases hm : x ∈ rs <;> simp [Nat.mod_two_ne_zero, hx, hm]

end Flapjack.Compiler.Backend.WordCse
