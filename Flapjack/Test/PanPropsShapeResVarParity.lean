import Flapjack.Pancake.Semantics.PanProps

/-!
# Direct-HOL parity for the exact `panProps` shape/`res_var` lemmas

Reproduces the original-HOL oracle rows in
`scripts/hol-probes/pan_props_shape_res_var_probe.out` (`spv_one`, `rv_hit`,
`rv_miss`, `rv_diff`, `rv_some`) over the exact `MlString`-keyed
`ValueHOL`/`resVarHOLExact` carriers, and applies each of the four tagged
lemmas `shapeOfHOLExact_val`, `resVarHOLExact_flookup`,
`resVarHOLExact_flookup_of_ne`, `resVarHOLExact_flookup_some_eq_lookup`.
It also reproduces the rows in
`scripts/hol-probes/pan_props_size_with_ctxt_probe.out` (`ssc_one`,
`ssc_comb2`, `ssc_nested`, `ssc_wf_one`, `ssc_wf_nested`, `ssc_eq_one`,
`ssc_eq_nested`) and applies the tagged `sizeOfShapeWithContextHOL_eq`.
-/

namespace Flapjack.Test.PanPropsShapeResVarParity

open Flapjack
open Flapjack.Pancake.PanLang

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

-- HOL `ssc_one = 1`.
def sizeWithCtxtOne : Nat :=
  sizeOfShapeWithContextHOL ([] : StructContextExact) ShapeHOL.one

-- HOL `ssc_comb2 = 2`.
def sizeWithCtxtComb2 : Nat :=
  sizeOfShapeWithContextHOL ([] : StructContextExact) (.comb [.one, .one])

-- HOL `ssc_nested = 3`.
def sizeWithCtxtNested : Nat :=
  sizeOfShapeWithContextHOL ([] : StructContextExact) (.comb [.one, .comb [.one, .one]])

-- HOL `ssc_wf_one = T` / `ssc_wf_nested = T`.
def wfOne : Bool :=
  isWfShapeExactHOL ([] : StructContextExact) ShapeHOL.one

def wfNested : Bool :=
  isWfShapeExactHOL ([] : StructContextExact) (.comb [.one, .comb [.one, .one]])

-- HOL `ssc_eq_one = T` / `ssc_eq_nested = T`.
def sizeEqOne : Bool :=
  sizeWithCtxtOne == sizeOfShapeHOL ShapeHOL.one

def sizeEqNested : Bool :=
  sizeWithCtxtNested == sizeOfShapeHOL (.comb [.one, .comb [.one, .one]])

/-- Combined parity check: the seven direct HOL `size_of_sh_with_ctxt` rows. -/
def sizeWithCtxtGuard : Bool :=
  (sizeWithCtxtOne == 1) && (sizeWithCtxtComb2 == 2) && (sizeWithCtxtNested == 3) &&
    wfOne && wfNested && sizeEqOne && sizeEqNested

#guard sizeWithCtxtGuard

/-- Fixture: HOL `size_of_sh_with_ctxt_eq` (`panPropsScript.sml:184`). -/
theorem sizeWithCtxt_fixture (shape : ShapeHOL) (context : StructContextExact)
    (h : isWfShapeExactHOL ([] : StructContextExact) shape = true) :
    sizeOfShapeWithContextHOL context shape = sizeOfShapeHOL shape :=
  sizeOfShapeWithContextHOL_eq shape context h

-- HOL `lfs_val = T` / `lfs_two = T` / `lfs_nested = T`.
def lfsVal : Bool :=
  (flattenHOL (.val (.word 5) : ValueHOL 64)).length ==
    sizeOfShapeHOL (shapeOfHOLExact (.val (.word 5) : ValueHOL 64))

/-- A two-field exact struct value. -/
def structTwo : ValueHOL 64 :=
  .rStruct [.val (.word 1), .val (.word 2)]

/-- A nested exact struct value. -/
def structNested : ValueHOL 64 :=
  .rStruct [.rStruct [.val (.word 1)], .val (.word 2)]

def lfsTwo : Bool :=
  (flattenHOL structTwo).length == sizeOfShapeHOL (shapeOfHOLExact structTwo)

def lfsNested : Bool :=
  (flattenHOL structNested).length == sizeOfShapeHOL (shapeOfHOLExact structNested)

-- HOL `lfs_val_len = 1` / `lfs_nested_len = 2`.
def lfsValLen : Bool := (flattenHOL (.val (.word 5) : ValueHOL 64)).length == 1

def lfsNestedLen : Bool := (flattenHOL structNested).length == 2

-- HOL `lfs_wf_nested = T`.
def lfsWfNested : Bool :=
  isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact structNested)

/-- Combined parity check: the six direct HOL `length_flatten` rows. -/
def lengthFlattenGuard : Bool :=
  lfsVal && lfsTwo && lfsNested && lfsValLen && lfsNestedLen && lfsWfNested

#guard lengthFlattenGuard

/-- Fixture: HOL `length_flatten_eq_size_of_shape` (`panPropsScript.sml:171`). -/
theorem lengthFlatten_fixture (v : ValueHOL 64)
    (h : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v) :=
  flattenHOL_length_eq_sizeOfShapeHOL v h

def runChecks : IO Bool := do
  if shapeResVarGuard && sizeWithCtxtGuard && lengthFlattenGuard then
    IO.println
      "PASS exact panProps shape_of_val / FLOOKUP_pan_res_var / size_of_sh_with_ctxt / length_flatten (18 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panProps shape/res_var/size/length_flatten lemmas"
    pure false

end Flapjack.Test.PanPropsShapeResVarParity
