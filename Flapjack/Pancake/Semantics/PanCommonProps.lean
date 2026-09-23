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