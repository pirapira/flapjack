import Flapjack.Pancake.Semantics.PanCommonProps

/-!
Parity checks for the exact port of HOL `fm_empty_zip_alist` in
`Flapjack/Pancake/Semantics/PanCommonProps.lean`.

Direct HOL-EVAL rows in `scripts/hol-probes/fm_empty_zip_alist_probe.out`:

```
fold_flookup_eq=T
flookup_first=SOME 20
flookup_absent=NONE
```
-/

namespace Flapjack.Test.FmEmptyZipAlistParity

open Flapjack

def xs : List Nat := [1, 2, 3]

def ys : List Nat := [10, 20, 30]

theorem xsNodup : xs.Nodup := by decide

theorem xsLength : xs.length = ys.length := by decide

/-- The zipped list fold agrees with the HOL `alist_to_fmap` right fold at a
    present key. -/
theorem foldFlookupEq :
    FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 2 =
      FLOOKUP (alistToFmap (xs.zip ys)) 2 := by
  rw [fmEmptyZipAlist xs ys xsLength xsNodup]

example : FUPDATE_LIST FEMPTY (xs.zip ys) = alistToFmap (xs.zip ys) :=
  fmEmptyZipAlist xs ys xsLength xsNodup

/-- Fold/fmap equality restricted to the concrete oracle lookups. -/
def parityGuard : Bool :=
  (FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 2 == some 20) &&
  (FLOOKUP (alistToFmap (xs.zip ys)) 2 == some 20) &&
  (FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 9 == none) &&
  (FLOOKUP (alistToFmap (xs.zip ys)) 9 == none)

#guard parityGuard

#eval parityGuard

/-- Exact HOL `MAX_LIST_add_not_mem` port: `maxList xs + 1` is never in `xs`. -/
theorem maxListAddNotMem : maxList xs + 1 ∉ xs :=
  MAX_LIST_add_not_mem xs

/-- Exact HOL `MAX_LIST_i_genlist` port: `maxList (List.range n) = n - 1`. -/
theorem maxListRange : maxList (List.range 5) = 5 - 1 :=
  MAX_LIST_i_genlist 5

def maxListGuard : Bool :=
  (!(xs.contains (maxList xs + 1))) && (maxList (List.range 5) == 4)

#guard maxListGuard

def runChecks : IO Bool := do
  let ok := parityGuard && maxListGuard
  IO.println (if ok then "PASS Crep fm_empty_zip_alist fold/alist equality matches HOL"
    else "FAIL Crep fm_empty_zip_alist fold/alist equality matches HOL")
  return ok

end Flapjack.Test.FmEmptyZipAlistParity