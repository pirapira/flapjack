import Flapjack.Pancake.Semantics.CrepProps

/-!
Parity checks for the `crepProps` assigned-variable theorems ported into
`Flapjack/Pancake/Semantics/CrepProps.lean`:

* `assigned_free_vars_IMP_assigned_vars`
* `nested_seq_assigned_vars_eq`
* `nested_seq_assigned_free_vars_eq`

The concrete programs mirror the direct HOL-EVAL rows in
`scripts/hol-probes/crep_assigned_vars_probe.out`:

```
afv_prog=[2; 3]
av_prog=[1; 2; 3]
imp_mem=T
imp_mem_absent=T
nested_av=[1; 2]
nested_afv=[1; 2]
```
-/

namespace Flapjack.Test.CrepAssignedVarsParity

open Flapjack

/-- `Dec 1 (Const 1) (Seq (Assign 2 (Var 1)) (Assign 3 (Const 2)))`. -/
def parityProg : CrepProg Nat :=
  .dec 1 (.const 1) (.seq (.assign 2 (.var 1)) (.assign 3 (.const 2)))

/-- `nested_seq (MAP2 Assign [1, 2] [Const 1, Const 2])`. -/
def parityNested : CrepProg Nat :=
  crepNestedSeq
    ([1, 2].zipWith (fun name value => CrepProg.assign name value)
      [CrepExp.const (1 : Nat), CrepExp.const 2])

theorem afvProg : crepAssignedFreeVars parityProg = [2, 3] := by
  simp [parityProg, crepAssignedFreeVars]

theorem avProg : crepAssignedVars parityProg = [1, 2, 3] := by
  simp [parityProg, crepAssignedVars]

theorem nestedAv : crepAssignedVars parityNested = [1, 2] := by
  simp [parityNested, crepNestedSeq, crepAssignedVars]

theorem nestedAfv : crepAssignedFreeVars parityNested = [1, 2] := by
  simp [parityNested, crepNestedSeq, crepAssignedFreeVars]

theorem impMem : (2 ∈ crepAssignedFreeVars parityProg →
    2 ∈ crepAssignedVars parityProg) := by
  rw [afvProg, avProg]
  decide

theorem impMemAbsent : (9 ∈ crepAssignedFreeVars parityProg →
    9 ∈ crepAssignedVars parityProg) := by
  rw [afvProg, avProg]
  decide

example : 2 ∈ crepAssignedVars parityProg :=
  mem_crepAssignedFreeVars_imp_mem_crepAssignedVars parityProg 2
    (by rw [afvProg]; decide)

example : crepAssignedVars parityNested = [1, 2] :=
  crepAssignedVars_nestedSeq_assign_zipWith [1, 2]
    [CrepExp.const (1 : Nat), CrepExp.const 2] (by decide)

example : crepAssignedFreeVars parityNested = [1, 2] :=
  crepAssignedFreeVars_nestedSeq_assign_zipWith [1, 2]
    [CrepExp.const (1 : Nat), CrepExp.const 2] (by decide)

/-- Exact-carrier (`CrepProgHOL`) sampling of the HOL rows `nested_av=[1; 2]`
    and `nested_afv=[1; 2]` in `scripts/hol-probes/crep_assigned_vars_probe.out`. -/
example : crepAssignedVarsHOL
    (crepNestedSeqHOL
      ([1, 2].zipWith (fun name value => CrepProgHOL.assign name value)
        [.const (1 : BitVec 64), .const (2 : BitVec 64)])) = [1, 2] :=
  crepAssignedVarsHOL_nestedSeq_assign_zipWith [1, 2]
    [.const (1 : BitVec 64), .const (2 : BitVec 64)] (by decide)

example : crepAssignedFreeVarsHOL
    (crepNestedSeqHOL
      ([1, 2].zipWith (fun name value => CrepProgHOL.assign name value)
        [.const (1 : BitVec 64), .const (2 : BitVec 64)])) = [1, 2] :=
  crepAssignedFreeVarsHOL_nestedSeq_assign_zipWith [1, 2]
    [.const (1 : BitVec 64), .const (2 : BitVec 64)] (by decide)

/-- Width-indexed production programme used to exercise the kernel bridges. -/
def parityNestedW : CrepProg (BitVec 64) :=
  crepNestedSeq
    ([1, 2].zipWith (fun name value => CrepProg.assign name value)
      [CrepExp.const (1 : BitVec 64), CrepExp.const 2])

/-- The kernel bridges relate the exact helpers to the executable ones. -/
example : crepAssignedVarsHOL (crepProgToHOL parityNestedW) =
    crepAssignedVars parityNestedW :=
  crepProgToHOL_crepAssignedVars parityNestedW

example : crepAssignedFreeVarsHOL (crepProgToHOL parityNestedW) =
    crepAssignedFreeVars parityNestedW :=
  crepProgToHOL_crepAssignedFreeVars parityNestedW

/-- The exact `assigned_free_vars_IMP_assigned_vars` port over `CrepProgHOL` and
    its production bridge, exercising the transferred membership. -/
example : 2 ∈ crepAssignedVarsHOL
    (crepNestedSeqHOL
      ([1, 2].zipWith (fun name value => CrepProgHOL.assign name value)
        [.const (1 : BitVec 64), .const (2 : BitVec 64)])) :=
  crepAssignedFreeVarsHOL_imp_crepAssignedVarsHOL _ 2 (by
    rw [crepAssignedFreeVarsHOL_nestedSeq_assign_zipWith [1, 2]
      [.const (1 : BitVec 64), .const (2 : BitVec 64)] (by decide)]
    decide)

example : 2 ∈ crepAssignedVars parityNestedW :=
  crepAssignedFreeVars_imp_crepAssignedVars_via_HOL parityNestedW 2 (by
    rw [parityNestedW, crepAssignedFreeVars_nestedSeq_assign_zipWith [1, 2]
      [CrepExp.const (1 : BitVec 64), CrepExp.const 2] (by decide)]
    decide)

/-- Width-indexed `W`-wrapper spot checks (beads `.18.4.3.85`): each HOL
    crepProps theorem restated over `CrepProg (BitVec 64)`/`CrepExp (BitVec 64)`. -/
example : ((List.range 3).map (CrepExp.var (α := BitVec 64))).flatMap crepExpVarsW =
    List.range 3 :=
  map_var_crepExpVars_eqW (width := 64) (List.range 3)

example : (loadGlobalsW (width := 64) (0 : BitVec 5) 2).length = 2 :=
  loadGlobals_lengthW (width := 64) 0 2

example : (loadGlobalsW (width := 64) (0 : BitVec 5) 2).flatMap crepExpVarsW = [] :=
  loadGlobals_crepExpVars_emptyW (width := 64) 0 2

example : crepAssignedFreeVarsW
    (crepNestedSeqW (storeGlobalsW (0 : BitVec 5) [.const (7 : BitVec 64)])) = [] :=
  crepAssignedFreeVars_nestedSeq_storeGlobalsW (width := 64) 0 [.const 7]

example : crepAssignedVarsW
    (crepNestedSeqW (storeGlobalsW (0 : BitVec 5) [.const (7 : BitVec 64)])) = [] :=
  crepAssignedVars_nestedSeq_storeGlobalsW (width := 64) 0 [.const 7]

example : crepAssignedVarsW
    (crepNestedSeqW (([1, 2].zipWith
      (fun name value => CrepProg.assign name value)
      [.const (3 : BitVec 64), .const (4 : BitVec 64)]))) = [1, 2] :=
  crepAssignedVars_nestedSeq_assign_zipWithW (width := 64) [1, 2]
    [.const (3 : BitVec 64), .const (4 : BitVec 64)]
    (by decide)

example : crepAssignedFreeVarsW
    (crepNestedSeqW (([1, 2].zipWith
      (fun name value => CrepProg.assign name value)
      [.const (3 : BitVec 64), .const 4]))) = [1, 2] :=
  crepAssignedFreeVars_nestedSeq_assign_zipWithW (width := 64) [1, 2]
    [.const (3 : BitVec 64), .const (4 : BitVec 64)]
    (by decide)

example : crepAssignedFreeVarsW
    (crepNestedSeqW
      (storeGlobalsW (width := 64) (0 : BitVec 5) ([] : List (CrepExp (BitVec 64))))) = [] :=
  crepAssignedFreeVars_nestedSeq_storeGlobalsW (width := 64) 0 []

def parityGuard : Bool :=
  (crepAssignedFreeVars parityProg == [2, 3]) &&
  (crepAssignedVars parityProg == [1, 2, 3]) &&
  (decide ((2 : Nat) ∈ ([2, 3] : List Nat) → 2 ∈ [1, 2, 3])) &&
  (decide ((9 : Nat) ∈ ([2, 3] : List Nat) → 9 ∈ [1, 2, 3])) &&
  (crepAssignedVars parityNested == [1, 2]) &&
  (crepAssignedFreeVars parityNested == [1, 2])

#guard parityGuard

#eval parityGuard

def runChecks : IO Bool := do
  let ok := parityGuard
  IO.println (if ok then "PASS Crep assigned-vars IMP and nested-seq theorems match HOL"
    else "FAIL Crep assigned-vars IMP and nested-seq theorems match HOL")
  return ok

end Flapjack.Test.CrepAssignedVarsParity