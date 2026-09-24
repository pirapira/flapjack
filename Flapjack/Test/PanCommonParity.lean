import Flapjack.Pancake.CrepLang

/-!
# Original-domain parity for `pan_common$distinct_lists`

The expected values are the direct HOL-EVAL observations in
`scripts/hol-probes/pan_common_distinct_lists_probe.out`, from
`cakeml/pancake/pan_commonScript.sml:8-11`:

```
Definition distinct_lists_def:
  distinct_lists xs ys = EVERY (\x. ~MEM x ys) xs
End
```

The current executable Flapjack form is `Flapjack.distinctLists`
(`Flapjack/Pancake/CrepLang.lean`), the same `EVERY`/`MEM` test specialised to
`Nat`. The exact polymorphic `@[hol]` rendering and its bridge to
`ListDisjoint` arrive with the tagged `distinctListsHol` port; this fixture
pins the executable Boolean behaviour against the original HOL rows.
-/

namespace Flapjack.Test.PanCommonParity

open Flapjack

/-- Bridge matching the probe's `distinct_eq_disjoint` row: the Boolean
    `distinct_lists` is equivalent to the propositional disjointness HOL
    proves via `distinct_lists_eq_disjoint`. -/
theorem distinctLists_eq_true_iff_listDisjoint (xs ys : List Nat) :
    distinctLists xs ys = true ↔ ListDisjoint xs ys := by
  simp only [distinctLists, List.all_eq_true, ListDisjoint]
  constructor
  · intro h value hv hw
    have hv' := h value hv
    rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hv'
    exact hv' hw
  · intro h value hv
    have : ¬ value ∈ ys := fun hw => h value hv hw
    rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    exact this

/-- The seven `pan_common_distinct_lists_probe.out` rows reproduced through the
    executable `Flapjack.distinctLists`. -/
def parityGuard : Bool :=
  distinctLists [1, 2] [3, 4] &&
  !(distinctLists [1, 2] [2, 4]) &&
  !(distinctLists [5, 1, 2] [4, 5]) &&
  distinctLists [] [1, 2] &&
  distinctLists [1, 2] [] &&
  (distinctLists [1, 2, 3] [4, 5] == [1, 2, 3].all (fun x => !([4, 5].contains x)))

#eval parityGuard
#guard parityGuard

/-- `distinct_eq_disjoint`: the same row through the HOL `distinct_lists`
    boundary HOL proves (`distinct_lists [1;2;3] [4;5] = DISJOINT (set …) (set …)`). -/
example : (distinctLists [1, 2, 3] [4, 5] = true) ↔
    ListDisjoint [1, 2, 3] [4, 5] :=
  distinctLists_eq_true_iff_listDisjoint [1, 2, 3] [4, 5]

example : distinctLists [1, 2, 3] [4, 5] = true := by decide
example : distinctLists [] [1, 2] = true := by decide
example : distinctLists [1, 2] [] = true := by decide
example : distinctLists [1, 2] [2, 4] = false := by decide
example : distinctLists [5, 1, 2] [4, 5] = false := by decide
example : distinctLists [1, 2, 3] [4, 5] =
    [1, 2, 3].all (fun x => !([4, 5].contains x)) := rfl

end Flapjack.Test.PanCommonParity
