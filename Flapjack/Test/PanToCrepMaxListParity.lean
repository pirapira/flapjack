import Flapjack.PanToCrepMaxList

/-!
# Original-domain parity for HOL `rich_list$MAX_LIST`

Fixtures mirror the original Pancake helper theorems
`MAX_LIST_APPEND` / `MAX_LIST_NOT_MEM`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4472-4482`).
-/

namespace Flapjack.Test.PanToCrepMaxListParity

open Flapjack

def first : List Nat := [3, 7, 1]
def second : List Nat := [9, 4]

theorem maxList_append_fixture :
    maxList (first ++ second) = max (maxList first) (maxList second) :=
  maxList_append first second

theorem maxList_append_value_fixture : maxList (first ++ second) = 9 := by
  rw [maxList_append_fixture]
  decide

theorem maxList_not_mem_fixture : (10 : Nat) ∉ first :=
  maxList_not_mem 10 first (by decide)

#guard maxList first = 7
#guard maxList (first ++ second) = 9
#guard decide ((10 : Nat) ∉ first)

end Flapjack.Test.PanToCrepMaxListParity
