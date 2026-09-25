/-
Parity fixtures for the exact port of HOL `panLang$size_of_sh_with_ctxt`
(`cakeml/pancake/panLangScript.sml:164-171`) over the faithful
`ShapeHOL`/`StructContextExact`/`StructInfoHOLExact` carriers (bead
flapjack-pxn.18.5.17.1.3.1).  Rows mirror
`scripts/hol-probes/pan_lang_size_of_sh_with_ctxt_probe.out`.
-/
import Flapjack.Pancake.PanLang.Decl

namespace Flapjack.Test.PanLangShapeSizeWithContextParity

open Flapjack.Pancake.PanLang

/-- The two-structure context used by the HOL oracle (`A` size 5, `B` size 3). -/
private def demoContext : StructContextExact :=
  [ (Flapjack.Basis.Pure.MlString.ofString "A", { fields := [], size := 5 }),
    (Flapjack.Basis.Pure.MlString.ofString "B", { fields := [], size := 3 }) ]

private def nameA : MlS := Flapjack.Basis.Pure.MlString.ofString "A"
private def nameZ : MlS := Flapjack.Basis.Pure.MlString.ofString "Z"

example : sizeOfShapeWithContextHOL demoContext .one = 1 := rfl

example : sizeOfShapeWithContextHOL demoContext (.named nameA) = 5 := by decide

example : sizeOfShapeWithContextHOL demoContext (.named nameZ) = 1 := by decide

example : sizeOfShapeWithContextHOL demoContext
    (.comb [.one, .named nameA, .named (Flapjack.Basis.Pure.MlString.ofString "B")]) = 9 := by decide

example : sizeOfShapeWithContextHOL demoContext
    (.comb [.one, .named nameZ]) = 2 := by decide

/-- Kernel-checked guard mirroring the five HOL oracle rows. -/
def shapeSizeGuard : Bool :=
  (sizeOfShapeWithContextHOL demoContext .one == 1) &&
  (sizeOfShapeWithContextHOL demoContext (.named nameA) == 5) &&
  (sizeOfShapeWithContextHOL demoContext (.named nameZ) == 1) &&
  (sizeOfShapeWithContextHOL demoContext
      (.comb [.one, .named nameA, .named (Flapjack.Basis.Pure.MlString.ofString "B")]) == 9) &&
  (sizeOfShapeWithContextHOL demoContext (.comb [.one, .named nameZ]) == 2)

#eval shapeSizeGuard
#guard shapeSizeGuard

def runChecks : IO Bool := do
  if shapeSizeGuard then
    IO.println "PASS panLang size_of_sh_with_ctxt exact carrier matches all 5 oracle rows"
    pure true
  else
    IO.println "FAIL panLang size_of_sh_with_ctxt exact carrier"
    pure false

end Flapjack.Test.PanLangShapeSizeWithContextParity
