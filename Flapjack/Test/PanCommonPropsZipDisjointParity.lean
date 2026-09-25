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

def runChecks : IO Bool := do
  if zipGuard then
    IO.println
      "PASS exact pan_commonProps zip fupdate not-mem and disjoint take/drop (3 HOL rows)"
    return true
  else
    IO.println "FAIL exact pan_commonProps zip fupdate not-mem and disjoint take/drop"
    return false

end Flapjack.Test.PanCommonPropsZipDisjointParity
