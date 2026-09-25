import Flapjack.Pancake.Semantics.PanProps

/-!
# Direct-HOL parity for the exact `panProps` shape/`res_var` lemmas

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/pan_props_shape_res_var_probe.out` (`spv_one`, `rv_hit`,
`rv_miss`, `rv_diff`, `rv_some`) over the exact `MlString`-keyed
`ValueHOL`/`resVarHOLExact` carriers, and applies each of the four tagged
lemmas `shapeOfHOLExact_val`, `resVarHOLExact_flookup`,
`resVarHOLExact_flookup_of_ne`, `resVarHOLExact_flookup_some_eq_lookup`.
-/

namespace Flapjack.Test.PanPropsShapeResVarParity

open Flapjack

/-- The faithful HOL `mlstring` of a source string. -/
abbrev ml (s : String) : Flapjack.Pancake.PanLang.MlS :=
  Flapjack.Basis.Pure.MlString.ofString s

/-- Concrete exact locals: `x = 3`. -/
def locals : Flapjack.Pancake.PanLang.MlS → Option (ValueHOL 64) :=
  fun name => if name = ml "x" then some (.val (.word 3)) else none

/-- A `ValueHOL` result projected to a natural, for guard comparison. -/
def wordOf (result : Option (ValueHOL 64)) : Option Nat :=
  match result with
  | some (.val (.word value)) => some value.toNat
  | _ => none

/-- Whether a `ShapeHOL` is the `One` constructor. -/
def isOneShape (shape : Flapjack.Pancake.PanLang.ShapeHOL) : Bool :=
  match shape with
  | .one => true
  | _ => false

-- HOL `spv_one = One`.
def shapeVal : Bool :=
  isOneShape (shapeOfHOLExact (.val (.word 5) : ValueHOL 64))

-- HOL `rv_hit = SOME (ValWord 7w)`.
def resVarHit : Bool :=
  wordOf (resVarHOLExact (width := 64) locals (ml "x", some (.val (.word 7))) (ml "x"))
    == some 7

-- HOL `rv_miss = SOME (ValWord 3w)`.
def resVarMiss : Bool :=
  wordOf (resVarHOLExact (width := 64) locals (ml "y", some (.val (.word 7))) (ml "x"))
    == some 3

-- HOL `rv_diff = T`.
def resVarDiff : Bool :=
  wordOf (resVarHOLExact (width := 64) locals (ml "y", none) (ml "x"))
    == wordOf (locals (ml "x"))

-- HOL `rv_some = T`.
def resVarSome : Bool :=
  wordOf (resVarHOLExact (width := 64) locals (ml "x", locals (ml "x")) (ml "x"))
    == wordOf (locals (ml "x"))

/-- Combined parity check: all five direct HOL rows above. -/
def shapeResVarGuard : Bool :=
  shapeVal && resVarHit && resVarMiss && resVarDiff && resVarSome

#guard shapeResVarGuard

/-- Fixture: HOL `shape_of_val` (`shape_of (Val _) = One`). -/
theorem shapeVal_fixture :
    shapeOfHOLExact (.val (.word 5) : ValueHOL 64) =
      Flapjack.Pancake.PanLang.ShapeHOL.one :=
  shapeOfHOLExact_val (.word 5)

/-- Fixture: HOL `FLOOKUP_pan_res_var_thm`. -/
theorem resVar_flookup_fixture (m n : Flapjack.Pancake.PanLang.MlS)
    (v : Option (ValueHOL 64)) :
    resVarHOLExact (width := 64) locals (m, v) n = if n = m then v else locals n :=
  resVarHOLExact_flookup locals m n v

/-- Fixture: HOL `flookup_res_var_diff_eq_org`. -/
theorem resVar_flookup_of_ne_fixture (n m : Flapjack.Pancake.PanLang.MlS)
    (v : Option (ValueHOL 64)) (h : n ≠ m) :
    resVarHOLExact (width := 64) locals (n, v) m = locals m :=
  resVarHOLExact_flookup_of_ne locals n m v h

/-- Fixture: HOL `flookup_res_var_some_eq_lookup`. -/
theorem resVar_flookup_some_eq_lookup_fixture
    (lc lc' : Flapjack.Pancake.PanLang.MlS → Option (ValueHOL 64))
    (v : Flapjack.Pancake.PanLang.MlS) (value : ValueHOL 64)
    (h : resVarHOLExact (width := 64) lc (v, lc' v) v = some value) :
    lc' v = some value :=
  resVarHOLExact_flookup_some_eq_lookup lc lc' v value h

def runChecks : IO Bool := do
  if shapeResVarGuard then
    IO.println
      "PASS exact panProps shape_of_val / FLOOKUP_pan_res_var (5 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panProps shape/res_var lemmas"
    pure false

end Flapjack.Test.PanPropsShapeResVarParity
