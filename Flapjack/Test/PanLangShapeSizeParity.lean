import Flapjack.Pancake.PanLang.Shape

/-!
# Exact HOL `size_of_shape` parity

Direct-oracle parity checks for the tagged exact port
`Flapjack.Pancake.PanLang.sizeOfShapeHOL` of HOL
`panLang$size_of_shape` (`cakeml/pancake/panLangScript.sml:174-177`).

Oracle rows (`scripts/hol-probes/pan_lang_size_of_shape_probe.out`):

```
ss_one=1
ss_comb=3
ss_named=1
ss_eq=T
```
-/

namespace Flapjack.Test.PanLangShapeSizeParity

open Flapjack
open Flapjack.Pancake.PanLang

/-- `«A»` as an exact `mlstring`. -/
private def nameA : MlS := Flapjack.Basis.Pure.MlString.ofString "A"

/-- `Comb [One; Comb [One; One]]`. -/
private def nested : ShapeHOL :=
  .comb [.one, .comb [.one, .one]]

example : sizeOfShapeHOL (.one : ShapeHOL) = 1 := by decide

example : sizeOfShapeHOL nested = 3 := by decide

example : sizeOfShapeHOL (.named nameA) = 1 := by decide

example : sizeOfShapeHOL nested = 3 := by decide

/-- Executable mirror of the four oracle rows. -/
private def shapeSizeGuard : Bool :=
  (sizeOfShapeHOL (.one : ShapeHOL) == 1) &&
  (sizeOfShapeHOL nested == 3) &&
  (sizeOfShapeHOL (.named nameA) == 1) &&
  ((sizeOfShapeHOL nested == 3) == true)

#eval shapeSizeGuard
#guard shapeSizeGuard

def runChecks : IO Bool := do
  if shapeSizeGuard then
    IO.println "PASS panLang size_of_shape exact carrier matches all 4 oracle rows"
    pure true
  else
    IO.println "FAIL panLang size_of_shape exact carrier"
    pure false

end Flapjack.Test.PanLangShapeSizeParity