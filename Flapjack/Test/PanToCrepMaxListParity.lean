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

theorem maxList_ge_of_mem_fixture : (3 : Nat) ≤ maxList first :=
  maxList_ge_of_mem first 3 (by decide)

theorem maxList_add_one_not_mem_fixture : maxList first + 1 ∉ first :=
  maxList_add_one_not_mem first

theorem maxList_range_fixture : maxList (List.range 5) = 4 :=
  maxList_range 5

theorem maxList_genlist_add_suc_val_fixture :
    maxList ((List.range 5).map (fun x => (x + 1) + 3)) = 8 :=
  maxList_genlist_add_suc_val 3 5 (by decide)

#check @maxList_ge_of_mem
#check @maxList_add_one_not_mem
#check @maxList_range
#check @maxList_genlist_add_suc_val

#guard maxList first = 7
#guard maxList (first ++ second) = 9
#guard decide ((10 : Nat) ∉ first)
#guard maxList ((List.range 5).map (fun x => (x + 1) + 3)) == 8

end Flapjack.Test.PanToCrepMaxListParity
