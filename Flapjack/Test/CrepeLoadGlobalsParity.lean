import Flapjack.Crepe
import Flapjack.CrepeGlobalStoreCorrectness

/-!
# Original-domain parity for `crepLang$load_globals`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_load_globals_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:116-120`.
-/

namespace Flapjack.Test.CrepeLoadGlobalsParity

open Flapjack

def isEmpty : List (CrepExp Nat) → Bool
  | [] => true
  | _ => false

def isOne : List (CrepExp Nat) → Bool
  | [.loadGlob 3] => true
  | _ => false

def isThree : List (CrepExp Nat) → Bool
  | [.loadGlob 3, .loadGlob 4, .loadGlob 5] => true
  | _ => false

def parityGuard : Bool :=
  isEmpty (loadGlobals 3 1 0) &&
  isOne (loadGlobals 3 1 1) &&
  isThree (loadGlobals 3 1 3)

#eval parityGuard
#guard parityGuard

/-- Cake `crepProps$length_load_globals_eq_read_size` on the parity fixture. -/
theorem loadGlobals_length_fixture : (loadGlobals 3 1 3).length = 3 :=
  loadGlobals_length 3 1 3

/-- Cake `crepProps$el_load_globals_elem` on the parity fixture: element `1`
    reads address `3 + 1 * 1 = 4`. -/
theorem loadGlobals_getElem_fixture :
    (loadGlobals 3 1 3)[1]? = some (.loadGlob 4) := by
  simpa using loadGlobals_getElem 3 1 3 1 (by decide)

/-- Cake `pan_to_crep$load_shape_el_rel` on the parity fixture: element `1`
    reads address `3 + 1 * 1 = 4`. -/
theorem loadShape_getElem_fixture :
    (loadShape 3 1 3 (.const 7))[1]? =
      some (.load (.op .add [.const 7, .const 4])) := by
  simpa using loadShape_getElem 3 1 3 1 (.const 7) (by decide)

/-- Cake `crepProps$length_load_shape_eq_shape` on the parity fixture. -/
theorem loadShape_length_fixture :
    (loadShape 3 1 3 (.const 7)).length = 3 :=
  loadShape_length 3 1 3 (.const 7)

/-- Cake `crepProps$map_var_cexp_eq_var` on a concrete variable list. -/
theorem map_var_crepExpVars_eq_fixture :
    (([2, 5, 9] : List Nat).map (CrepExp.var (α := Nat))).flatMap crepExpVars =
      [2, 5, 9] :=
  map_var_crepExpVars_eq (α := Nat) [2, 5, 9]

/-- Cake `crepProps$var_exp_load_shape` on the parity fixture. -/
theorem crepExpVars_of_mem_loadShape_fixture :
    crepExpVars (α := Nat) (.load (.op .add [.var 5, .const 3])) =
      crepExpVars (α := Nat) (.var 5) :=
  crepExpVars_of_mem_loadShape (α := Nat) 3 1 1 (.var 5)
    (.load (.op .add [.var 5, .const 3])) (by simp [loadShape])

/-- Cake `crepProps$load_glob_not_mem_load` on the parity fixture. -/
theorem crepExps_loadShape_not_mem_loadGlob_fixture :
    CrepExp.loadGlob (3 : Nat) ∉ (loadShape 3 1 2 (CrepExp.var 5)).flatMap crepExps :=
  crepExps_loadShape_not_mem_loadGlob (α := Nat) 3 1 2 (.var 5) 3 (by simp [crepExps])

/-- Cake `crepProps$nested_seq_assigned_free_vars_eq` on a concrete list. -/
theorem crepAssignedFreeVars_nestedSeq_assign_zipWith_fixture :
    crepAssignedFreeVars
        (crepNestedSeq
          (([2, 5] : List Nat).zipWith (fun name value => CrepProg.assign name value)
            ([CrepExp.const 1, CrepExp.const 2] : List (CrepExp Nat)))) =
      [2, 5] :=
  crepAssignedFreeVars_nestedSeq_assign_zipWith (α := Nat) [2, 5]
    [CrepExp.const 1, CrepExp.const 2] rfl

/-- Cake `crepProps$assigned_free_vars_seq_store_empty` on a concrete store list. -/
theorem crepAssignedFreeVars_nestedSeq_stores_fixture :
    crepAssignedFreeVars
        (crepNestedSeq (stores (CrepExp.const 3) [CrepExp.const 7] 0 1)) = [] :=
  crepAssignedFreeVars_nestedSeq_stores (α := Nat) (CrepExp.const 3)
    [CrepExp.const 7] 0 1

/-- Cake `crepProps$assigned_free_vars_store_globals_empty` on a concrete list. -/
theorem crepAssignedFreeVars_nestedSeq_storeGlobals_fixture :
    crepAssignedFreeVars
        (crepNestedSeq (storeGlobals 3 1 [CrepExp.const 7, CrepExp.const 8])) = [] :=
  crepAssignedFreeVars_nestedSeq_storeGlobals (α := Nat) 3 1
    [CrepExp.const 7, CrepExp.const 8]

/-- Cake `crepProps$assigned_vars_nested_decs_append` on a concrete list. -/
theorem crepAssignedVars_nestedDecs_append_fixture :
    crepAssignedVars
        (nestedDecs [2, 5] [CrepExp.const 1, CrepExp.const 2] CrepProg.skip) =
      [2, 5] := by
  simpa [crepAssignedVars] using crepAssignedVars_nestedDecs_append (α := Nat) [2, 5]
    [CrepExp.const 1, CrepExp.const 2] CrepProg.skip rfl

/-- Cake `crepProps$assigned_free_vars_nested_decs_append` on a concrete list. -/
theorem crepAssignedFreeVars_nestedDecs_append_fixture :
    crepAssignedFreeVars
        (nestedDecs [2, 5] [CrepExp.const 1, CrepExp.const 2] CrepProg.skip) =
      [] := by
  simpa [crepAssignedFreeVars] using crepAssignedFreeVars_nestedDecs_append (α := Nat) [2, 5]
    [CrepExp.const 1, CrepExp.const 2] CrepProg.skip rfl

/-- Cake `crepProps$nested_seq_assigned_vars_eq` on a concrete list. -/
theorem crepAssignedVars_nestedSeq_assign_zipWith_fixture :
    crepAssignedVars
        (crepNestedSeq
          (([2, 5] : List Nat).zipWith (fun name value => CrepProg.assign name value)
            ([CrepExp.const 1, CrepExp.const 2] : List (CrepExp Nat)))) =
      [2, 5] :=
  crepAssignedVars_nestedSeq_assign_zipWith (α := Nat) [2, 5]
    [CrepExp.const 1, CrepExp.const 2] rfl

/-- Cake `crepProps$assigned_vars_seq_store_empty` on a concrete store list. -/
theorem crepAssignedVars_nestedSeq_stores_fixture :
    crepAssignedVars
        (crepNestedSeq (stores (CrepExp.const 3) [CrepExp.const 7] 0 1)) = [] :=
  crepAssignedVars_nestedSeq_stores (α := Nat) (CrepExp.const 3)
    [CrepExp.const 7] 0 1

/-- Cake `crepProps$assigned_vars_store_globals_empty` on a concrete list. -/
theorem crepAssignedVars_nestedSeq_storeGlobals_fixture :
    crepAssignedVars
        (crepNestedSeq (storeGlobals 3 1 [CrepExp.const 7, CrepExp.const 8])) = [] :=
  crepAssignedVars_nestedSeq_storeGlobals (α := Nat) 3 1
    [CrepExp.const 7, CrepExp.const 8]

theorem loadGlobals_crepExpVars_empty_fixture :
    (loadGlobals 3 1 3).flatMap crepExpVars = [] :=
  loadGlobals_crepExpVars_empty (α := Nat) 3 1 3

theorem mem_crepAssignedFreeVars_imp_mem_crepAssignedVars_fixture :
    (3 : Nat) ∈ crepAssignedVars (CrepProg.assign 3 (CrepExp.const 1)) :=
  mem_crepAssignedFreeVars_imp_mem_crepAssignedVars
    (CrepProg.assign 3 (CrepExp.const 1)) 3 (by simp [crepAssignedFreeVars])

/-! A concrete execution witness for Cake
    `pan_to_crepProps$evaluate_nested_decs_load_globals`.  The memory map is
    the oracle for two generated global loads; the body is `skip`, so the
    theorem checks both expression-prefix evaluation and local installation. -/
def loadGlobalsState : CrepState Nat :=
  { locals := fun _ => none
    memory := fun address =>
      if address == 0 then some 10 else if address == 1 then some 11 else none
    globals := fun address =>
      if address == 0 then some 10 else if address == 1 then some 11 else none }

def loadGlobalsPrimitive : CrepPrimitiveHandler Nat := fun _ _ => none

def loadGlobalsFfi : CrepFfiHandler Nat := fun _ _ _ _ _ _ => none

def loadGlobalsSharedMem : CrepSharedMemHandler Nat := fun _ _ _ _ => none

def loadGlobalsNames : List Nat := [1, 2]

def loadGlobalsValues : List Nat := [10, 11]

def loadGlobalsResultState : CrepState Nat :=
  { loadGlobalsState with
      locals := updateCrepLocalList loadGlobalsState.locals
        loadGlobalsNames loadGlobalsValues }

theorem crepNestedDecsEval_loadGlobals_fixture :
    CrepNestedDecsEval [] loadGlobalsPrimitive loadGlobalsFfi
      loadGlobalsSharedMem 0 0 1 loadGlobalsState loadGlobalsNames
      (loadGlobals 0 1 2) .skip (.normal loadGlobalsResultState) := by
  apply crepNestedDecsEval_loadGlobals_of_evalExps
    (values := loadGlobalsValues)
  · simp [loadGlobalsNames]
  · simp [loadGlobalsState, loadGlobalsValues, loadGlobals,
      evalCrepFullExps, evalCrepFullExp]
  · simp [loadGlobalsResultState, loadGlobalsState, loadGlobalsNames,
      loadGlobalsValues, updateCrepLocalList, evalCrepFullProg]

theorem evalCrepFullProg_nestedDecs_loadGlobals_fixture :
    evalCrepFullProg [] loadGlobalsPrimitive loadGlobalsFfi
      loadGlobalsSharedMem 0 0 (1 + loadGlobalsNames.length)
      loadGlobalsState
      (nestedDecs loadGlobalsNames (loadGlobals 0 1 2) .skip) =
      some (restoreCrepResultList loadGlobalsState.locals loadGlobalsNames
        (.normal loadGlobalsResultState)) := by
  apply evalCrepFullProg_nestedDecs_loadGlobals_of_evalExps
    (values := loadGlobalsValues)
  · simp [loadGlobalsNames]
  · simp [CrepDistinctNames, loadGlobalsNames]
  · simp [loadGlobalsState, loadGlobalsValues, loadGlobals,
      evalCrepFullExps, evalCrepFullExp]
  · simp [loadGlobalsResultState, loadGlobalsState, loadGlobalsNames,
      loadGlobalsValues, updateCrepLocalList, evalCrepFullProg]

theorem crepNestedDecsStateEval_loadGlobals_fixture :
    CrepNestedDecsStateEval [] loadGlobalsPrimitive loadGlobalsFfi
      loadGlobalsSharedMem 0 0 1 loadGlobalsState loadGlobalsNames
      (loadGlobals 0 1 2) .skip (.normal loadGlobalsResultState) := by
  apply crepNestedDecsStateEval_loadGlobals_of_evalExps
    (values := loadGlobalsValues)
  · simp [loadGlobalsNames]
  · simp [loadGlobalsState, loadGlobalsValues, loadGlobals,
      evalCrepFullExpsState, evalCrepFullExpState]
  · simp [loadGlobalsResultState, loadGlobalsState, loadGlobalsNames,
      loadGlobalsValues, updateCrepLocalList, evalCrepFullProgState]

theorem evalCrepFullProgState_nestedDecs_loadGlobals_fixture :
    evalCrepFullProgState [] loadGlobalsPrimitive loadGlobalsFfi
      loadGlobalsSharedMem 0 0 (1 + loadGlobalsNames.length)
      loadGlobalsState
      (nestedDecs loadGlobalsNames (loadGlobals 0 1 2) .skip) =
      some (restoreCrepResultList loadGlobalsState.locals loadGlobalsNames
        (.normal loadGlobalsResultState)) := by
  apply evalCrepFullProgState_nestedDecs_loadGlobals_of_evalExps
    (values := loadGlobalsValues)
  · simp [loadGlobalsNames]
  · simp [CrepDistinctNames, loadGlobalsNames]
  · simp [loadGlobalsState, loadGlobalsValues, loadGlobals,
      evalCrepFullExpsState, evalCrepFullExpState]
  · simp [loadGlobalsResultState, loadGlobalsState, loadGlobalsNames,
      loadGlobalsValues, updateCrepLocalList, evalCrepFullProgState]

#check @not_mem_crepAssignedFreeVars_nestedDecs

theorem not_mem_crepAssignedFreeVars_nestedDecs_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (nestedDecs [2, 5] [CrepExp.const 1, CrepExp.const 2]
        (CrepProg.assign 3 (CrepExp.const 4))) :=
  not_mem_crepAssignedFreeVars_nestedDecs [2, 5]
    [CrepExp.const 1, CrepExp.const 2] (CrepProg.assign 3 (CrepExp.const 4))
    (by decide) (by simp) (by simp [crepAssignedFreeVars])

#check @crepAssignedFreeVars_assignRet

theorem crepAssignedFreeVars_assignRet_fixture :
    crepAssignedFreeVars (assignRet (1 : Nat) [2, 5, 9]) = [2, 5, 9] :=
  crepAssignedFreeVars_assignRet (1 : Nat) [2, 5, 9]

def runChecks : IO Bool := do
  let results := [
    isEmpty (loadGlobals 3 1 0),
    isOne (loadGlobals 3 1 1),
    isThree (loadGlobals 3 1 3)]
  match results with
  | [empty, one, three] =>
      if empty then IO.println "PASS crep load_globals empty" else IO.println "FAIL crep load_globals empty"
      if one then IO.println "PASS crep load_globals one" else IO.println "FAIL crep load_globals one"
      if three then IO.println "PASS crep load_globals three" else IO.println "FAIL crep load_globals three"
      pure (empty && one && three)
  | _ =>
      IO.println "FAIL crep load_globals result arity"
      pure false

end Flapjack.Test.CrepeLoadGlobalsParity
