import Flapjack.HolRef
import Flapjack.PanToCrepMaxList

/-! Exact theorem counterpart for CakeML's `crep_inlineProofScript.sml`.

    The declarations here are stated over Lean's `(List.range n).map f`, the
    image of HOL's `GENLIST f n`, and over `Nat`, matching the source's
    `:num` variables. Each carries the HOL declaration name and argument
    order verbatim. -/

namespace Flapjack

/-- CakeML's `genlist_less_than` (`crep_inlineProofScript.sml:629`): every value
    in `GENLIST (λx. a + SUC x) n` is strictly above `a`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_less_than"]
theorem genlist_less_than (n a v : Nat) :
    v ∈ (List.range n).map (fun x => a + (x + 1)) → a < v := by
  intro hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  omega

/-- CakeML's `genlist_not_in` (`crep_inlineProofScript.sml:636`): values at or
    below `a` do not occur in `GENLIST (λx. a + SUC x) n`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_not_in"]
theorem genlist_not_in (n a v : Nat) (h : v ≤ a) :
    v ∉ (List.range n).map (fun x => a + (x + 1)) := by
  intro hmem
  have := genlist_less_than n a v hmem
  omega

/-- CakeML's `genlist_all_distinct` (`crep_inlineProofScript.sml:643`):
    `GENLIST (λx. a + SUC x) n` has no duplicates. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_all_distinct"]
theorem genlist_all_distinct (n a : Nat) :
    ((List.range n).map (fun x => a + (x + 1))).Nodup :=
  List.Pairwise.map (fun x => a + (x + 1))
    (fun _left _right hne heq =>
      hne (Nat.add_right_cancel (Nat.add_left_cancel heq)))
    List.nodup_range

/-- CakeML's `MORE_THEN_NOT_MAX_LIST` (`crep_inlineProofScript.sml:1562`): a
    value strictly above `MAX_LIST l` does not occur in `l`.  Lean's `maxList`
    is the faithful port of HOL's `rich_list$MAX_LIST`
    (`Flapjack/PanToCrepMaxList.lean`), so this is the same fact as HOL's
    `MAX_LIST_NOT_MEM`, stated here under the `crep_inline` declaration name. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MORE_THEN_NOT_MAX_LIST"]
theorem moreThenNotMaxList (l : List Nat) (x : Nat) (h : maxList l < x) :
    x ∉ l :=
  maxList_not_mem x l (by omega)

end Flapjack
