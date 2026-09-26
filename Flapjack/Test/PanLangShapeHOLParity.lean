import Flapjack.Pancake.PanLang.Shape
import Flapjack.Basis.Pure.MlString

/-!
Parity fixture for the exact `panLang$shape` carrier
(`Flapjack/Pancake/PanLang/Shape.lean`, `ShapeHOL`).

The rows reproduce the direct HOL EVAL fixture
`scripts/hol-probes/pan_lang_shape_probe.out`, which evaluates
`panLang$shape_to_str` at concrete shapes and pins the `named` field as an
`mlstring` (`Named nm` returns `nm`).  Lean-side we run the same computation
through `shapeOfHOL` (the exact carrier -> production `String` shape) and
`Flapjack.Shape.shapeToString`.
-/

namespace Flapjack.Test.PanLangShapeHOLParity

open Flapjack
open Flapjack.Pancake.PanLang

private def ofString := Flapjack.Basis.Pure.MlString.ofString

mutual
  private def shapeListBEq : List ShapeHOL → List ShapeHOL → Bool
    | [], [] => true
    | x :: xs, y :: ys => shapeHOLBEq x y && shapeListBEq xs ys
    | _, _ => false

  private def shapeHOLBEq : ShapeHOL → ShapeHOL → Bool
    | .one, .one => true
    | .comb a, .comb b => shapeListBEq a b
    | .named a, .named b => a = b
    | _, _ => false
end

/-- Row `shp_one_str`: `shape_to_str One = "1"`. -/
private def oneRow : Bool :=
  Shape.shapeToString (shapeOfHOL (.one : ShapeHOL)) = "1"

/-- Row `shp_named_str`: `shape_to_str (Named (strlit "Foo")) = "Foo"`. -/
private def namedRow : Bool :=
  Shape.shapeToString (shapeOfHOL (.named (ofString "Foo"))) = "Foo"

/-- Row `shp_comb_str`: `shape_to_str (Comb [One; Named "Bar"]) = "{1,Bar}"`. -/
private def combRow : Bool :=
  Shape.shapeToString (shapeOfHOL (.comb [.one, .named (ofString "Bar")])) = "{1,Bar}"

/-- Row `shp_named_explode`: the `named` field is the `mlstring` name itself,
so exploding it yields the three bytes of `"Foo"`. -/
private def explodeRow : Bool :=
  (ofString "Foo").explode.length = 3

/-- Row `shp_named_eq`: constructor equality on the exact carrier. -/
private def namedEqRow : Bool :=
  shapeHOLBEq (.named (ofString "Foo")) (.named (ofString "Foo")) = true

/-- Row `shp_named_ne`. -/
private def namedNeRow : Bool :=
  shapeHOLBEq (.named (ofString "Foo")) (.named (ofString "Bar")) = false

/-- Row `shp_comb_len`: the `Comb` field is a two-element `shape list`. -/
private def combLenRow : Bool :=
  ([.one, .named (ofString "Bar")] : List ShapeHOL).length = 2

private def parityGuard : Bool :=
  oneRow && namedRow && combRow && explodeRow && namedEqRow && namedNeRow && combLenRow

#eval parityGuard
#guard parityGuard

/-- The exact carrier round trips through production syntax and back. -/
example : shapeToHOL (shapeOfHOL (.named (ofString "Foo"))) =
    (.named (ofString "Foo") : ShapeHOL) :=
  shapeToHOL_shapeOfHOL _

example : shapeToHOL (shapeOfHOL (.comb [.one, .named (ofString "Bar")])) =
    (.comb [.one, .named (ofString "Bar")] : ShapeHOL) :=
  shapeToHOL_shapeOfHOL _

/-- The reverse direction is exact on byte-ranged production shapes; this is
the documented side condition. -/
example (s : Shape) (h : ShapeByteRanged s) : shapeOfHOL (shapeToHOL s) = s :=
  shapeOfHOL_shapeToHOL s h

/-- Production diagnostic rendering is the exact HOL rendering after decoding
the reviewed MlString port on the byte-ranged domain. -/
example :
    Shape.shapeToString (.comb [.one, .named "Bar", .comb [.one, .one]]) =
      Flapjack.Basis.Pure.MlString.toStringOfBytes
        (shapeToStrHOL
          (shapeToHOL (.comb [.one, .named "Bar", .comb [.one, .one]]))) := by
  exact shapeToString_eq_shapeToStrHOL_toStringOfBytes _ (by
    simp [ShapeByteRanged])

end Flapjack.Test.PanLangShapeHOLParity
