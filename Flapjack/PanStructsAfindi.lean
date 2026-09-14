import Flapjack.Static

/-!
Faithful executable port of CakeML Pancake's `pan_structs$afindi` helper.
`afindi` returns the first zero-based position of a key in an association
list, preserving the original first-match behavior on duplicate keys.
-/

namespace Flapjack

def afindi [BEq α] (key : α) : List (α × β) → Option Nat
  | [] => none
  | (candidate, _) :: entries =>
      if key == candidate then some 0
      else match afindi key entries with
        | none => none
        | some index => some (index + 1)
termination_by entries => sizeOf entries
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

end Flapjack
