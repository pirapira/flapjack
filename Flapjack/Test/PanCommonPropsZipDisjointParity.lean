import Flapjack.Pancake.Semantics.PanCommonProps

/-!
# Direct-HOL parity for the exact `pan_commonProps` zip/fupdate and disjoint
take/drop lemmas

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/pan_common_props_zip_disjoint_probe.out` (`fzn_notmem`,
`fzn_mem`, `fzn_preserved`, `dtd_disjoint`, `ddt_disjoint`) over the exact
`FiniteMap`/`ListDisjoint` carriers.
-/

namespace Flapjack.Test.PanCommonPropsZipDisjointParity

open Flapjack

/-- `f = FEMPTY |+ (3, 30)` as in the HOL probe. -/
def baseMap : FiniteMap Nat Nat := FUPDATE FEMPTY (3, 30)

/-- `ZIP ([1;2], [10;20])` as in the HOL probe. -/
def zipEntries : List (Nat × Nat) := [1, 2].zip [10, 20]

def updatedMap : FiniteMap Nat Nat := FUPDATE_LIST baseMap zipEntries

-- HOL `fzn_notmem = T`.
def fznNotMem : Bool := FLOOKUP updatedMap 9 == FLOOKUP baseMap 9

-- HOL `fzn_mem = SOME 10`.
def fznMem : Bool := FLOOKUP updatedMap 1 == some 10

-- HOL `fzn_preserved = T`.
def fznPreserved : Bool := FLOOKUP updatedMap 3 == FLOOKUP baseMap 3

def zipGuard : Bool := fznNotMem && fznMem && fznPreserved

#guard zipGuard

/-- HOL `flookup_fupdate_zip_not_mem` (`pan_commonPropsScript.sml:289`). -/
theorem flookup_fupdate_zip_not_mem_fixture :
    FLOOKUP (FUPDATE_LIST baseMap ([1, 2].zip [10, 20])) 9 = FLOOKUP baseMap 9 :=
  flookup_fupdate_zip_not_mem [1, 2] [10, 20] baseMap 9 (by decide) (by decide)

/-- HOL `disjoint_take_drop_sum` (`pan_commonPropsScript.sml:399`). -/
theorem disjoint_take_drop_sum_fixture :
    ListDisjoint (([1, 2, 3, 4] : List Nat).take 2)
      ((([1, 2, 3, 4] : List Nat).drop (2 + 1)).take 1) :=
  disjoint_take_drop_sum 2 1 1 [1, 2, 3, 4] (by decide)

/-- HOL `disjoint_drop_take_sum` (`pan_commonPropsScript.sml:413`). -/
theorem disjoint_drop_take_sum_fixture :
    ListDisjoint ((([1, 2, 3, 4] : List Nat).drop (2 + 1)).take 1)
      (([1, 2, 3, 4] : List Nat).take 2) :=
  disjoint_drop_take_sum 2 1 1 [1, 2, 3, 4] (by decide)

/-- `lhs = FEMPTY |+ (1,10) |+ (2,20) |+ (1,10) |+ (2,22)` from the HOL probe. -/
def diffVarsLhs : FiniteMap Nat Nat :=
  FUPDATE (FUPDATE (FUPDATE (FUPDATE FEMPTY (1, 10)) (2, 20)) (1, 10)) (2, 22)

/-- `rhs = FEMPTY |+ (1,10) |+ (2,22)`. -/
def diffVarsRhs : FiniteMap Nat Nat := FUPDATE (FUPDATE FEMPTY (1, 10)) (2, 22)

-- HOL `fmdv_eq_1/2/3 = T`, `fmdv_lhs_a = SOME 10`, `fmdv_lhs_b = SOME 22`,
-- `fmdv_lhs_absent = NONE`.
def fmdvGuard : Bool :=
  (FLOOKUP diffVarsLhs 1 == FLOOKUP diffVarsRhs 1) &&
    (FLOOKUP diffVarsLhs 2 == FLOOKUP diffVarsRhs 2) &&
    (FLOOKUP diffVarsLhs 3 == FLOOKUP diffVarsRhs 3) &&
    (FLOOKUP diffVarsLhs 1 == some 10) &&
    (FLOOKUP diffVarsLhs 2 == some 22) &&
    (FLOOKUP diffVarsLhs 3 == none)

#guard fmdvGuard

/-- HOL `fm_update_diff_vars` (`pan_commonPropsScript.sml:780`). -/
theorem fm_update_diff_vars_fixture :
    FUPDATE (FUPDATE (FUPDATE (FUPDATE FEMPTY (1, 10)) (2, 20)) (1, 10)) (2, 22) =
      FUPDATE (FUPDATE FEMPTY (1, 10)) (2, 22) :=
  fm_update_diff_vars FEMPTY 1 2 10 20 22 (by decide)

def runChecks : IO Bool := do
  if zipGuard && fmdvGuard then
    IO.println
      "PASS exact pan_commonProps zip fupdate not-mem, disjoint take/drop, and fm_update_diff_vars (9 HOL rows)"
    return true
  else
    IO.println "FAIL exact pan_commonProps zip fupdate not-mem, disjoint take/drop, and fm_update_diff_vars"
    return false

end Flapjack.Test.PanCommonPropsZipDisjointParity
