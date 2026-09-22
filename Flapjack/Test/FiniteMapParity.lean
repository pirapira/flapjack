import Flapjack.FiniteMap

/-!
Regressions for the faithful finite-map layer used by
`localRel_le_zip_update_preserved` (`pan_to_crepProofScript.sml:2263`).
-/

namespace Flapjack.Test.FiniteMapParity

open Flapjack

#guard FLOOKUP (FUPDATE (FEMPTY : FiniteMap Nat Nat) (3, 7)) 3 == some 7
#guard FLOOKUP (FUPDATE (FEMPTY : FiniteMap Nat Nat) (3, 7)) 4 == none
#guard FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat) [(1, 10), (2, 20)]) 2 == some 20
#guard FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat) [(1, 10), (2, 20)]) 1 == some 10

/-- Cake `FLOOKUP_UPDATE` on a concrete map. -/
theorem fupdate_fixture :
    FLOOKUP (FUPDATE (FEMPTY : FiniteMap Nat Nat) (3, 7)) 3 = some 7 := by
  simp [FLOOKUP_update]

/-- Cake `FUPDATE_LIST_THM` on a concrete map. -/
theorem fupdate_list_fixture :
    FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat) [(1, 10), (2, 20)]) 2 = some 20 := by
  simp [FUPDATE_LIST_cons, FLOOKUP_update, FUPDATE_LIST_nil]

/-- Cake `opt_mmap_some_eq_zip_flookup` on a concrete map. -/
theorem opt_mmap_some_eq_zip_flookup_fixture :
    ([1, 2] : List Nat).mapM
        (fun key =>
          FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat)
            (([1, 2] : List Nat).zip ([10, 20] : List Nat))) key) = some [10, 20] :=
  opt_mmap_some_eq_zip_flookup [1, 2] (FEMPTY : FiniteMap Nat Nat) [10, 20]
    (by decide) rfl

/-- A concrete base map for the disjoint-update regression. -/
def baseMap : FiniteMap Nat Nat :=
  FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat) [(3, 30), (4, 40)]

/-- Cake `opt_mmap_disj_zip_flookup` on a concrete map. -/
theorem opt_mmap_disj_zip_flookup_fixture :
    ([3, 4] : List Nat).mapM
        (fun key =>
          FLOOKUP (FUPDATE_LIST baseMap
            (([1, 2] : List Nat).zip ([10, 20] : List Nat))) key) = some [30, 40] := by
  rw [opt_mmap_disj_zip_flookup [1, 2] baseMap [3, 4] [10, 20]
    (by intro value hin hin'; simp [List.mem_cons] at hin hin'; omega) rfl]
  simp [baseMap, FUPDATE_LIST_cons, FUPDATE_LIST_nil, FLOOKUP_update]

#check @FLOOKUP_update
#check @FUPDATE_LIST_cons
#check @FUPDATE_FUPDATE_LIST_commutes
#check @opt_mmap_some_eq_zip_flookup
#check @opt_mmap_disj_zip_flookup
#check @localsRel
#check @localsRel_lookup_ctxt
#check @localRel_le_zip_update_preserved
#check @listDisjoint_range_add
#check @listDisjoint_range_add_shift

/-- Cake `genlist_distinct_max` on a concrete instance. -/
theorem listDisjoint_range_add_fixture :
    ListDisjoint (((List.range 3).map (fun x => x + 1 + 4)) : List Nat) [0, 1, 2, 4] :=
  listDisjoint_range_add 3 4 [0, 1, 2, 4] (by intro y hy; simp [List.mem_cons] at hy; omega)

/-- Cake `genlist_distinct_max'` on a concrete instance. -/
theorem listDisjoint_range_add_shift_fixture :
    ListDisjoint (((List.range 3).map (fun x => x + 1 + (4 + 5))) : List Nat) [0, 1, 2, 4] :=
  listDisjoint_range_add_shift 3 4 5 [0, 1, 2, 4] (by intro y hy; simp [List.mem_cons] at hy; omega)

end Flapjack.Test.FiniteMapParity
