import Flapjack.FiniteMap.Basic
import Flapjack.HolRef

/-!
# Pancake `pan_common`

Lean counterpart of `cakeml/pancake/pan_commonScript.sml`.  The HOL script
defines the generic Boolean list predicate `distinct_lists` used by the
`pan_commonProps` context well-formedness lemmas.

HOL's `MEM` is true (definitional) list membership, so the faithful interface
uses `DecidableEq` and `decide` of membership rather than an arbitrary `BEq`.
The `BEq`-based executable implementation is provided as an untagged bridge
below.
-/

namespace Flapjack

/-- Exact port of HOL `distinct_lists_def`
    (`cakeml/pancake/pan_commonScript.sml:8`):
    `distinct_lists xs ys = EVERY (\x. ~MEM x ys) xs`, a Boolean predicate.
    HOL `MEM` is true list membership, so this uses `decide` on `∈` under a
    `DecidableEq` instance. -/
@[hol "cakeml/pancake/pan_commonScript.sml" "distinct_lists_def"]
def distinctListsHol {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => decide (x ∉ ys))

/-- Bridge between the exact Boolean predicate `distinctListsHol` and the
    propositional `ListDisjoint` used by `no_overlap` and production code. -/
theorem distinctListsHol_eq_true_iff_listDisjoint {α : Type} [DecidableEq α]
    (xs ys : List α) : distinctListsHol xs ys = true ↔ ListDisjoint xs ys := by
  simp only [distinctListsHol, List.all_eq_true, ListDisjoint, decide_eq_true_eq]

/-- Untagged implementation bridge: the `BEq`/`List.contains` executable form
    agrees with the exact `distinctListsHol` whenever `BEq` is lawful. -/
theorem distinctListsBEq_eq_distinctListsHol {α : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] (xs ys : List α) :
    (xs.all (fun x => !(ys.contains x))) = distinctListsHol xs ys := by
  simp only [distinctListsHol]
  congr 1
  funext x
  by_cases h : x ∈ ys
  · simp [List.contains_eq_mem, h]
  · simp [List.contains_eq_mem, h]

end Flapjack