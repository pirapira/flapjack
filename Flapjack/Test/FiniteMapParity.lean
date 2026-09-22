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

#check @localsRel_extend_new_var
#check @panValueNoOverlap_cons_of
#check @panValueCtxtMax_mono

/-- Cake `locals_rel_extend_new_var` on a concrete fresh variable. -/
theorem localsRel_extend_new_var_fixture :
    localsRel ([("x", (Shape.one, [1]))] : InfoMap (Shape × List Nat)) 1
      (FUPDATE (FEMPTY : FiniteMap String (PanValue Nat)) ("x", PanValue.word 5))
      (FUPDATE_LIST (FEMPTY : FiniteMap Nat Nat) (([1] : List Nat).zip ([5] : List Nat))) := by
  have hbase : localsRel ([] : InfoMap (Shape × List Nat)) 0
      (FEMPTY : FiniteMap String (PanValue Nat)) (FEMPTY : FiniteMap Nat Nat) :=
    ⟨panValueNoOverlap_empty, panValueCtxtMax_empty 0 (by omega),
      by intro vname v h; simp [FLOOKUP_empty] at h⟩
  have h := localsRel_extend_new_var ([] : InfoMap (Shape × List Nat)) 0
    (FEMPTY : FiniteMap String (PanValue Nat)) (FEMPTY : FiniteMap Nat Nat)
    "x" (PanValue.word 5) [1] hbase (by simp [panValueShape, isWfShape]) (by decide)
    (by
      intro slot hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl
      simp [panValueShape])
    (by simp [panValueShape])
  simpa [panValueShape, Shape.shapeSize, panValueFlatten] using h

/-! ### `FDOMSUB` / `resVar` regressions (Cake `res_var` layer) -/

#check @FDOMSUB
#check @resVar
#check @FLOOKUP_resVar
#check @FLOOKUP_resVar_diff_eq
#check @resVar_commutes

/-- A concrete finite map for the `res_var` regressions. -/
def resVarBase : FiniteMap Nat Nat := FUPDATE_LIST FEMPTY [(3, 30)]

/-- A concrete finite map with two entries. -/
def resVarBase2 : FiniteMap Nat Nat := FUPDATE_LIST FEMPTY [(3, 30), (4, 40)]

/-- `FDOMSUB` removes exactly the requested key. -/
theorem fdomsub_fixture :
    FLOOKUP (FDOMSUB resVarBase2 3) 3 = none
      ∧ FLOOKUP (FDOMSUB resVarBase2 3) 4 = some 40 := by
  constructor
  · simp [FDOMSUB, FLOOKUP]
  · simp [FDOMSUB, FLOOKUP, resVarBase2, FUPDATE_LIST, FUPDATE]

/-- Cake `flookup_res_var_thm` on a concrete map. -/
theorem flookup_resVar_fixture :
    FLOOKUP (resVar resVarBase (4, some 40)) 4 = some 40
      ∧ FLOOKUP (resVar resVarBase (4, some 40)) 3 = some 30 := by
  constructor
  · rw [FLOOKUP_resVar]; simp only [beq_iff_eq, if_true]
  · rw [FLOOKUP_resVar_diff_eq _ _ _ 40 (by decide)]
    simp [resVarBase, FLOOKUP, FUPDATE_LIST, FUPDATE]

/-- Cake `res_var_commutes` on a concrete map. -/
theorem resVar_commutes_fixture :
    resVar (resVar resVarBase (2, some 20)) (3, some 30)
      = resVar (resVar resVarBase (3, some 30)) (2, some 20) := by
  exact resVar_commutes resVarBase (FUPDATE_LIST FEMPTY [(2, 20), (3, 30)]) 3 2 (by decide)

/-- Cake `mk_ctxt_imp_locals_rel` at the empty context. -/
theorem localsRel_empty_fixture :
    localsRel ([] : InfoMap (Shape × List Nat)) 0
      (FEMPTY : FiniteMap String (PanValue Nat)) (FEMPTY : FiniteMap Nat Nat) :=
  localsRel_empty 0 (FEMPTY : FiniteMap Nat Nat)

#check @localsRel_empty
#check @localsRel_of_empty_source

/-- Cake `flookup_res_var_distinct_eq` on a concrete fold. -/
theorem FLOOKUP_foldl_resVar_not_mem_fixture :
    FLOOKUP (([(3, some 30), (4, some 40)] : List (Nat × Option Nat)).foldl resVar
      (FUPDATE_LIST FEMPTY [(2, 20)])) 2 = some 20 := by
  rw [FLOOKUP_foldl_resVar_not_mem]
  · simp [FLOOKUP, FUPDATE_LIST, FUPDATE]
  · simp

/-- Cake `flookup_res_var_distinct_zip_eq` on a concrete fold. -/
theorem FLOOKUP_foldl_resVar_zip_not_mem_fixture :
    FLOOKUP (([2, 5] : List Nat).zip ([some 20, some 50] : List (Option Nat)) |>.foldl resVar
      (FUPDATE_LIST FEMPTY [(3, 30)])) 3 = some 30 := by
  rw [FLOOKUP_foldl_resVar_zip_not_mem]
  · simp [FLOOKUP, FUPDATE_LIST, FUPDATE]
  · rfl
  · simp

/-- Cake `flookup_res_var_distinct` on a concrete fold. -/
theorem map_FLOOKUP_foldl_resVar_zip_fixture :
    ([3, 4] : List Nat).map (fun y =>
        FLOOKUP (([2, 5] : List Nat).zip ([some 20, some 50] : List (Option Nat)) |>.foldl resVar
          (FUPDATE_LIST FEMPTY [(3, 30), (4, 40)])) y) =
      ([3, 4] : List Nat).map (fun y =>
        FLOOKUP (FUPDATE_LIST FEMPTY [(3, 30), (4, 40)]) y) := by
  apply map_FLOOKUP_foldl_resVar_zip
  · intro value hvalue hvalue'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalue hvalue'
    omega
  · rfl

#check @FLOOKUP_foldl_resVar_not_mem
#check @FLOOKUP_foldl_resVar_zip_not_mem
#check @map_FLOOKUP_foldl_resVar_zip

end Flapjack.Test.FiniteMapParity
