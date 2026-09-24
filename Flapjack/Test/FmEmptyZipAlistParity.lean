import Flapjack.Pancake.Semantics.PanCommonProps

/-!
Parity checks for the exact ports of HOL `fm_empty_zip_alist` and
`fm_empty_zip_flookup` in `Flapjack/Pancake/Semantics/PanCommonProps.lean`.

Direct HOL-EVAL rows in `scripts/hol-probes/fm_empty_zip_alist_probe.out`:

```
fold_flookup_eq=T
flookup_first=SOME 20
flookup_absent=NONE
zip_lookup_witness=T
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

/-- The duplicate-free zip lookup exposes the common index (HOL
    `fm_empty_zip_flookup`). -/
theorem zipLookupWitness :
    ∃ (n : Nat) (hn : n < xs.length),
      (xs.zip ys)[n]'(by rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hn, xsLength ▸ hn⟩) =
        (3, 30) :=
  fmEmptyZipFlookup xs ys 3 30 xsLength xsNodup (by decide)

/-- Bool guard for the lookup-witness oracle row `zip_lookup_witness=T`. -/
def zipFlookupGuard : Bool :=
  (FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 3 == some 30) &&
  ((xs.zip ys)[2]? == some (3, 30))

#guard zipFlookupGuard

/-- Fold/fmap equality restricted to the concrete oracle lookups. -/
def parityGuard : Bool :=
  (FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 2 == some 20) &&
  (FLOOKUP (alistToFmap (xs.zip ys)) 2 == some 20) &&
  (FLOOKUP (FUPDATE_LIST FEMPTY (xs.zip ys)) 9 == none) &&
  (FLOOKUP (alistToFmap (xs.zip ys)) 9 == none)

#guard parityGuard

#eval parityGuard

/-! ### HOL `all_distinct_flookup_all_distinct` / `no_overlap_flookup_distinct` -/

/-- Direct HOL-EVAL rows in `scripts/hol-probes/pan_common_props_no_overlap_probe.out`. -/
example (fm : FiniteMap String (Shape × List Nat)) (x : String) (y : Shape)
    (zs : List Nat) (hno : noOverlap fm) (hlookup : FLOOKUP fm x = some (y, zs)) :
    zs.Nodup :=
  allDistinctFlookupAllDistinct fm x y zs hno hlookup

example (fm : FiniteMap String (Shape × List Nat)) (x y : String) (a b : Shape)
    (xs ys : List Nat) (hno : noOverlap fm) (hxy : x ≠ y)
    (hx : FLOOKUP fm x = some (a, xs)) (hy : FLOOKUP fm y = some (b, ys)) :
    distinctLists xs ys = true :=
  noOverlapFlookupDistinct fm x y a b xs ys hno hxy hx hy

/-- The concrete context used by the HOL oracle: `x ↦ [1,2]`, `y ↦ [3,4]`. -/
def noOverlapFm : FiniteMap String (Shape × List Nat) :=
  FUPDATE (FUPDATE (FEMPTY : FiniteMap String (Shape × List Nat))
    ("x", (Shape.one, [1, 2]))) ("y", (Shape.one, [3, 4]))

theorem noOverlapFm_x : FLOOKUP noOverlapFm "x" = some (Shape.one, [1, 2]) := by
  simp only [noOverlapFm, FLOOKUP, FUPDATE]
  rw [if_neg (by decide), if_pos (by decide)]

theorem noOverlapFm_x_nodup : ([1, 2] : List Nat).Nodup := by decide

/-- Disjointness of the two distinct variables' slots (`HOL slots_disjoint=T`). -/
def slotsDisjointGuard : Bool :=
  !(distinctLists [1, 2] [3, 4]) == false && distinctLists [1, 2] [3, 4]

#guard slotsDisjointGuard

/-- HOL `fm_empty_zip_flookup_el` oracle row `nested_zip_lookup=T`. -/
theorem nestedZipLookupEl :
    FLOOKUP (FUPDATE_LIST FEMPTY ([1, 2, 3].zip ([10, 20, 30].zip [100, 200, 300]))) 2 =
      some (20, 200) := by
  rw [fmEmptyZipFlookupEl [1, 2, 3] [10, 20, 30] [100, 200, 300] 1 2
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  decide


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
  let ok := parityGuard && zipFlookupGuard && maxListGuard
  IO.println (if ok then "PASS Crep fm_empty_zip_alist fold/alist equality and fm_empty_zip_flookup witness match HOL"
    else "FAIL Crep fm_empty_zip_alist fold/alist equality and fm_empty_zip_flookup witness match HOL")
  return ok

end Flapjack.Test.FmEmptyZipAlistParity