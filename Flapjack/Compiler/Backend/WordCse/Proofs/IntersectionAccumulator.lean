import Flapjack.Compiler.Backend.WordCse.Join
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Misc.BalancedMap.InsertCorrect
import Flapjack.Misc.BalancedMap.LookupSemantics

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Misc.BalancedMap

/-- Exact HOL `bm_inter_eq_acc_thm` (`word_cseProof:576-584`): for arbitrary
payloads and native trees, exactly the three `invariant listCmp` premises give
the output invariant and, for every semantic key set `ks`, the full `FLOOKUP`
equation over the reviewed `to_fmap` producer (canonical `lookup`). Proof
follows HOL's induction on `m1` generalising the accumulator. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "bm_inter_eq_acc_thm"
  (fmap_as_finite_support_result_observations := [Flapjack.Misc.BalancedMap.toFmap])]
theorem bmInterEqAccThm {α : Type} [DecidableEq α] (m2 m1 acc : Map (List Nat) α)
    (h : invariant listCmp m2 ∧ invariant listCmp m1 ∧ invariant listCmp acc) :
    invariant listCmp (bmInterEqAcc m2 m1 acc) ∧
    ∀ ks, (toFmap listCmp (bmInterEqAcc m2 m1 acc)).lookup ks =
      match (toFmap listCmp m1).lookup ks with
      | none => (toFmap listCmp acc).lookup ks
      | some v => if (toFmap listCmp m2).lookup ks = some v then some v
          else (toFmap listCmp acc).lookup ks := by
  classical
  obtain ⟨h2, h1, hacc⟩ := h
  induction m1 generalizing acc with
  | tip => exact ⟨hacc, fun ks => rfl⟩
  | bin n k v l r ihl ihr =>
    have clauses := (invariantEq (β := α) listCmp n k v l r).2.mp h1
    have hl := h1.2.2.2.2.1
    have hr := h1.2.2.2.2.2
    -- the conditionally extended accumulator
    have hacc1 : invariant listCmp
          (if lookup listCmp k m2 = some v then insert listCmp k v acc else acc) ∧
        ∀ ks, (toFmap listCmp
            (if lookup listCmp k m2 = some v then insert listCmp k v acc else acc)).lookup ks =
          if ks = keySet listCmp k ∧ lookup listCmp k m2 = some v then some v
          else (toFmap listCmp acc).lookup ks := by
      by_cases hk : lookup listCmp k m2 = some v
      · have ins := insertThm listCmp k v acc ⟨goodCmpListCmp, hacc⟩
        simp only [hk, if_true, and_true]
        refine ⟨ins.1, fun ks => ?_⟩
        rw [ins.2]
        simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      · rw [if_neg hk]
        exact ⟨hacc, fun ks => by rw [if_neg (fun h => hk h.2)]⟩
    obtain ⟨vr, er⟩ := ihr _ hr hacc1.1
    obtain ⟨vl, el⟩ := ihl _ hl vr
    refine ⟨vl, fun ks => ?_⟩
    simp only [bmInterEqAcc]
    rw [el ks, er ks, hacc1.2 ks]
    have hm2 : lookup listCmp k m2 = (toFmap listCmp m2).lookup (keySet listCmp k) :=
      lookupThm listCmp k m2 ⟨goodCmpListCmp, h2⟩
    simp only [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      HolFiniteMapExact.lookup_union]
    by_cases hks : ks = keySet listCmp k
    · subst hks
      have hln : (toFmap listCmp l).lookup (keySet listCmp k) = none := by
        by_contra hne
        exact clauses.2.1 goodCmpListCmp hne
      have hrn : (toFmap listCmp r).lookup (keySet listCmp k) = none := by
        by_contra hne
        exact clauses.2.2.1 goodCmpListCmp hne
      simp only [hln, hrn, if_true, true_and, hm2]
    · simp only [hks, if_false, false_and]
      cases hlk : (toFmap listCmp l).lookup ks with
      | none => simp only []
      | some w =>
        have hrk : (toFmap listCmp r).lookup ks = none := by
          by_contra hne
          exact Set.disjoint_left.mp (clauses.1 goodCmpListCmp)
            (show (toFmap listCmp l).lookup ks ≠ none by rw [hlk]; simp) hne
        simp only [hrk]

/-- Exact HOL `lookup_bm_inter_eq` (`word_cseProof:621-638`): for arbitrary
payloads, keys and values, exactly the two input invariants make a lookup in
the intersection succeed with `v` iff both input lookups do. Proof as in HOL,
from `bm_inter_eq_acc_thm` with the empty accumulator and `lookup_thm`. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_bm_inter_eq"]
theorem lookupBmInterEq {α : Type} [DecidableEq α] (m1 m2 : Map (List Nat) α)
    (k : List Nat) (v : α) (h : invariant listCmp m1 ∧ invariant listCmp m2) :
    (lookup listCmp k (bmInterEq m1 m2) = some v ↔
      lookup listCmp k m1 = some v ∧ lookup listCmp k m2 = some v) := by
  have hE : invariant listCmp (empty : Map (List Nat) α) := by simp [empty, invariant]
  obtain ⟨hv, he⟩ := bmInterEqAccThm m2 m1 empty ⟨h.2, h.1, hE⟩
  unfold bmInterEq
  rw [lookupThm listCmp k _ ⟨goodCmpListCmp, hv⟩, lookupThm listCmp k m1 ⟨goodCmpListCmp, h.1⟩,
    lookupThm listCmp k m2 ⟨goodCmpListCmp, h.2⟩, he]
  have h0 : (toFmap listCmp (empty : Map (List Nat) α)).lookup (keySet listCmp k) = none := rfl
  cases (toFmap listCmp m1).lookup (keySet listCmp k) with
  | none => simp [h0]
  | some w =>
    by_cases h2 : (toFmap listCmp m2).lookup (keySet listCmp k) = some w
    · simp only [h2, if_true, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, -⟩; rfl
    · simp only [h2, if_false, h0, reduceCtorEq, false_iff, not_and, Option.some.injEq]
      rintro rfl; exact h2

end Flapjack.Compiler.Backend.WordCse
