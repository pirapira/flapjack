import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
The exact finite-map port of `pan_to_crep$make_vmap`.

HOL (`cakeml/pancake/pan_to_crepScript.sml:327-334`) is

```
make_vmap params =
  let pvars = MAP FST params;
      shs   = MAP SND params;
      ns    = GENLIST I (size_of_shape (Comb shs));
      cvars = ZIP (shs, with_shape shs ns) in
   FEMPTY |++ ZIP (pvars, cvars)
```

so it returns a HOL finite map `varname |-> (shape # num list)` directly. Its
exact Lean counterpart therefore uses the reviewed canonical finite-map carrier
`HolFiniteMapExact MlS (ShapeHOL × List Nat)`, over the faithful `MlS` and
`ShapeHOL` carriers, with `GENLIST I` = `List.range`, `with_shape` =
`withShapeHOL`, `size_of_shape` = `sizeOfShapeHOL`, and `|++` =
`HolFiniteMapExact.updateList` (matching raw `FUPDATE_LIST`). Because the result
is a finite map directly (not a field of an owning structure), the declaration
carries the standalone `fmap_as_finite_support_result` qualifier, justified by
the same-module lookup witness `holFmapAsFiniteSupportResultWitness_panToCrepMakeVmapHOLExact`
against the raw function-backed counterpart `panToCrepMakeVmapRaw`.

The production boundary still builds its map with the `String`/`Shape`-keyed
`panToCrepMakeVmapHOL` in `Flapjack/Pancake/PanToCrep/Compile.lean`; the exact
carrier replacement of that production path is tracked by `flapjack-pxn.18.3.5.8`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL withShapeHOL sizeOfShapeHOL)

/-- Broad raw-function counterpart of `panToCrepMakeVmapHOLExact`: the same HOL `FEMPTY |++`
    construction as a raw `MlS → Option (ShapeHOL × List Nat)` lookup, with no
    finite-support guarantee. Flapjack-only infrastructure used as the broad
    side of the finite-support result witness. -/
def panToCrepMakeVmapRaw (params : List (MlS × ShapeHOL)) :
    MlS → Option (ShapeHOL × List Nat) :=
  let pvars := params.map Prod.fst
  let shs := params.map Prod.snd
  let ns := List.range (sizeOfShapeHOL (.comb shs))
  let cvars := shs.zip (withShapeHOL shs ns)
  FUPDATE_LIST (fun _ => none) (pvars.zip cvars)

/-- Exact port of HOL `pan_to_crep$make_vmap_def`
    (`cakeml/pancake/pan_to_crepScript.sml:327-334`). `MAP FST`/`MAP SND` are
    `List.map Prod.fst`/`Prod.snd`, `GENLIST I n` is `List.range n`,
    `size_of_shape (Comb shs)` is `sizeOfShapeHOL (.comb shs)`, `with_shape` is
    the tagged `withShapeHOL`, and `FEMPTY |++` is `HolFiniteMapExact.updateList`
    over `HolFiniteMapExact.empty` (the `FUPDATE_LIST` fold, later duplicates
    winning). The result is the canonical finite-support translation of the HOL
    finite map; the standalone qualifier is justified by the lookup witness
    below. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "make_vmap_def"
  (fmap_as_finite_support_result)]
def panToCrepMakeVmapHOLExact (params : List (MlS × ShapeHOL)) :
    HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  let pvars := params.map Prod.fst
  let shs := params.map Prod.snd
  let ns := List.range (sizeOfShapeHOL (.comb shs))
  let cvars := shs.zip (withShapeHOL shs ns)
  HolFiniteMapExact.updateList HolFiniteMapExact.empty (pvars.zip cvars)

/-- Standalone finite-map result witness for `panToCrepMakeVmapHOLExact`: its `lookup` is
    exactly the raw `FUPDATE_LIST`-backed HOL `make_vmap` lookup
    `panToCrepMakeVmapRaw`. Kernel-checked; the `fmap_as_finite_support_result` checker
    requires this declaration beside `panToCrepMakeVmapHOLExact`. -/
theorem holFmapAsFiniteSupportResultWitness_panToCrepMakeVmapHOLExact
    (params : List (MlS × ShapeHOL)) (key : MlS) :
    (panToCrepMakeVmapHOLExact params).lookup key = panToCrepMakeVmapRaw params key := by
  simp only [panToCrepMakeVmapHOLExact, panToCrepMakeVmapRaw, HolFiniteMapExact.lookup_updateList,
    HolFiniteMapExact.empty]

end Flapjack
