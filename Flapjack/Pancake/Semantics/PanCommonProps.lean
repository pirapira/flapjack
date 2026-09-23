import Flapjack.FiniteMap.Basic
import Flapjack.HolRef
import Flapjack.Pancake.PanLang

/-!
# Pancake `pan_commonProps`

Lean counterpart of `cakeml/pancake/semantics/pan_commonPropsScript.sml`.  The
HOL script contains the context well-formedness predicates shared by the
Pan-to-Crep correctness proof: `ctxt_max` bounds the variable slots and
`no_overlap` requires distinct variables to occupy disjoint slots.  Both are
stated over the extensional finite-map model from `Flapjack.FiniteMap.Basic`.
-/

namespace Flapjack

/-- HOL `ctxt_max_def` (`cakeml/pancake/semantics/pan_commonPropsScript.sml:11`):
    the slot bound is non-negative and every slot assigned by the context map
    is at most `n`. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "ctxt_max_def"]
def ctxtMax (n : Nat) (fm : FiniteMap String (Shape × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ v a xs, FLOOKUP fm v = some (a, xs) → ∀ x ∈ xs, x ≤ n

/-- HOL `no_overlap_def` (`cakeml/pancake/semantics/pan_commonPropsScript.sml:18`):
    every variable's slot list is duplicate-free, and variables whose slot sets
    intersect are the same variable. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "no_overlap_def"]
def noOverlap (fm : FiniteMap String (Shape × List Nat)) : Prop :=
  (∀ x a xs, FLOOKUP fm x = some (a, xs) → xs.Nodup) ∧
    ∀ x y a b xs ys, FLOOKUP fm x = some (a, xs) → FLOOKUP fm y = some (b, ys) →
      (∃ z, z ∈ xs ∧ z ∈ ys) → x = y

/-- HOL `opt_mmap_eq_some`: an optional map succeeds exactly when every
    element maps to the corresponding `some` value. -/
@[hol "cakeml/pancake/semantics/pan_commonPropsScript.sml" "opt_mmap_eq_some"]
theorem optMmapEqSome (xs : List α) (f : α → Option β) (ys : List β) :
    xs.mapM f = some ys ↔ xs.map f = ys.map some := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x xs ih =>
        cases hfx : f x with
        | none => simp [List.mapM_cons, hfx] at h
        | some value =>
            cases htail : xs.mapM f with
            | none => simp [List.mapM_cons, hfx, htail] at h
            | some rest =>
                have hpair : value :: rest = ys := by
                  simpa [List.mapM_cons, hfx, htail] using h
                cases ys with
                | nil => simp at hpair
                | cons y ys =>
                    simp only [List.cons.injEq] at hpair
                    rcases hpair with ⟨rfl, rfl⟩
                    simpa [hfx] using ih rest htail
  · intro h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x xs ih =>
        cases ys with
        | nil => simp at h
        | cons y ys =>
            simp only [List.map_cons, List.cons.injEq] at h
            rcases h with ⟨hfx, htail⟩
            simp [List.mapM_cons, hfx, ih ys htail]

/-- The empty context map satisfies `ctxt_max` for every bound. -/
theorem ctxtMax_empty (n : Nat) :
    ctxtMax n (FEMPTY : FiniteMap String (Shape × List Nat)) := by
  refine ⟨Nat.zero_le n, ?_⟩
  intro v a xs hlookup
  simp at hlookup

/-- The empty context map satisfies `no_overlap`. -/
theorem noOverlap_empty :
    noOverlap (FEMPTY : FiniteMap String (Shape × List Nat)) := by
  refine ⟨?_, ?_⟩
  · intro x a xs hlookup
    simp at hlookup
  · intro x y a b xs ys hx hy hinter
    simp at hx

end Flapjack
