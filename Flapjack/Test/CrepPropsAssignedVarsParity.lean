import Flapjack.Pancake.Semantics.CrepProps

/-!
# Direct-HOL parity for the exact `crepProps` assigned_vars / var_cexp lemmas

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/crep_props_assigned_vars_probe.out` (`avnda`, `afvnda`,
`avsse`, `afvsse`, `vels`) over the exact `CrepExp`/`CrepProg` carriers.
-/

namespace Flapjack.Test.CrepPropsAssignedVarsParity

open Flapjack

/-- The expression list `[Const 0; Var 1]` of the HOL probe. -/
def decValues : List (CrepExp (BitVec 64)) := [.const 0, .var 1]

/-- `nested_decs [1;2] [Const 0; Var 1] Skip`. -/
def nestedDecsProg : CrepProg (BitVec 64) := nestedDecs [1, 2] decValues .skip

/-- `nested_decs [1;2] [Const 0; Var 1] (Assign 9 (Var 3))`. -/
def nestedDecsBody : CrepProg (BitVec 64) := nestedDecs [1, 2] decValues (.assign 9 (.var 3))

/-- `nested_seq (stores (Var 0) [Const 5; Const 6] 0w)`. -/
def storesProg : CrepProg (BitVec 64) :=
  crepNestedSeq (storesW (.var 0) [.const 5, .const 6] (0 : BitVec 64))

-- HOL `avnda = [1; 2]`.
def avndaGuard : Bool := crepAssignedVars nestedDecsProg == [1, 2]

-- HOL `afvnda = [9]`.
def afvndaGuard : Bool := crepAssignedFreeVars nestedDecsBody == [9]

-- HOL `avsse = []`.
def avsseGuard : Bool := crepAssignedVars storesProg == []

-- HOL `afvsse = []`.
def afvsseGuard : Bool := crepAssignedFreeVars storesProg == []

-- HOL `vels = [[3]; [3]]`.
def velsGuard : Bool :=
  (loadShapeBytes (0 : BitVec 64) 2 (.var 3)).map crepExpVars == [[3], [3]]

def guardAll : Bool := avndaGuard && afvndaGuard && avsseGuard && afvsseGuard && velsGuard

#guard guardAll

/-- HOL `assigned_vars_nested_decs_append` (`crepPropsScript.sml:390`). -/
theorem crepAssignedVars_nestedDecs_appendW_fixture :
    crepAssignedVarsW (nestedDecsW [1, 2] decValues .skip) = [1, 2] := by
  rw [crepAssignedVars_nestedDecs_appendW _ _ _ (by simp [decValues])]
  simp [crepAssignedVarsW, crepAssignedVars]

/-- HOL `assigned_free_vars_nested_decs_append` (`crepPropsScript.sml:400`). -/
theorem crepAssignedFreeVars_nestedDecs_appendW_fixture :
    crepAssignedFreeVarsW (nestedDecsW [1, 2] decValues (.assign 9 (.var 3))) = [9] := by
  rw [crepAssignedFreeVars_nestedDecs_appendW _ _ _ (by simp [decValues])]
  simp [crepAssignedFreeVarsW, crepAssignedFreeVars]

/-- HOL `assigned_vars_seq_store_empty` (`crepPropsScript.sml:429`). -/
theorem crepAssignedVars_nestedSeq_storesW_fixture :
    crepAssignedVarsW
      (crepNestedSeqW (storesW (.var 0) [.const 5, .const 6] (0 : BitVec 64))) = [] :=
  crepAssignedVars_nestedSeq_storesW (.var 0) [.const 5, .const 6] (0 : BitVec 64)

/-- HOL `assigned_free_vars_seq_store_empty` (`crepPropsScript.sml:439`). -/
theorem crepAssignedFreeVars_nestedSeq_storesW_fixture :
    crepAssignedFreeVarsW
      (crepNestedSeqW (storesW (.var 0) [.const 5, .const 6] (0 : BitVec 64))) = [] :=
  crepAssignedFreeVars_nestedSeq_storesW (.var 0) [.const 5, .const 6] (0 : BitVec 64)

/-- HOL `var_exp_load_shape` (`crepPropsScript.sml:215`). -/
theorem crepExpVars_of_mem_loadShapeW_fixture :
    crepExpVars (CrepExp.load (CrepExp.var 3) : CrepExp (BitVec 64)) =
      crepExpVars (CrepExp.var 3 : CrepExp (BitVec 64)) :=
  crepExpVars_of_mem_loadShapeW (width := 64) 2 (0 : BitVec 64)
    (CrepExp.var 3) (CrepExp.load (CrepExp.var 3)) (by simp [loadShapeBytes])

def runChecks : IO Bool := do
  if guardAll then
    IO.println
      "PASS exact crepProps assigned_vars nested_decs/stores and var_exp load_shape (5 HOL rows)"
    return true
  else
    IO.println "FAIL exact crepProps assigned_vars nested_decs/stores and var_exp load_shape"
    return false

end Flapjack.Test.CrepPropsAssignedVarsParity
