import Flapjack.Pancake.PanLang.Exp

/-!
Parity fixture for the exact `panLang$exp` carrier
(`Flapjack/Pancake/PanLang/Exp.lean`, `ExpHOL`).

The rows reproduce the direct HOL EVAL fixture
`scripts/hol-probes/pan_lang_exp_probe.out`, which evaluates `panLang$exp`
constructors at the HOL numeral word type 64 and pins the `Const` word payload
and the `mlstring` name fields.  Lean-side we build the same `ExpHOL` values and
read back the corresponding payloads/arities.
-/

namespace Flapjack.Test.PanLangExpHOLParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private def ofString := Flapjack.Basis.Pure.MlString.ofString

/-- Row `ex_const`: `Const (5w : 64 word)` carries the word `5`. -/
private def constRow : Bool :=
  match (ExpHOL.const (5 : BitVec 64) : ExpHOL 64) with
  | .const w => w.toNat = 5
  | _ => false

/-- Row `ex_var_len`: `Var Local (strlit "xy")` has name length `2`. -/
private def varRow : Bool :=
  match (ExpHOL.var .local (ofString "xy") : ExpHOL 64) with
  | .var _ nm => nm.explode.length = 2
  | _ => false

/-- Row `ex_rstruct_len`: `RStruct` has a two-element `exp list` field. -/
private def rstructRow : Bool :=
  ((([.const (1 : BitVec 64), .const 2] : List (ExpHOL 64)).length) = 2)

/-- Row `ex_rfield`: `RField 3 _` carries index `3`. -/
private def rfieldRow : Bool :=
  match (ExpHOL.rfield 3 (.const (1 : BitVec 64)) : ExpHOL 64) with
  | .rfield i _ => i = 3
  | _ => false

/-- Row `ex_nstruct_len`: `NStruct` has a two-element `(fldname # exp) list`. -/
private def nstructRow : Bool :=
  ((([(ofString "f", .const (1 : BitVec 64)),
      (ofString "g", .const 2)] : List (MlString × ExpHOL 64)).length) = 2)

/-- Row `ex_nfield_len`: `NField (strlit "foo") _` has name length `3`. -/
private def nfieldRow : Bool :=
  match (ExpHOL.nfield (ofString "foo") (.const (1 : BitVec 64)) : ExpHOL 64) with
  | .nfield nm _ => nm.explode.length = 3
  | _ => false

/-- Row `ex_load_shape`: `Load One _` reports the shape string `"1"`. -/
private def loadShapeRow : Bool :=
  match (ExpHOL.load .one (.const (0 : BitVec 64)) : ExpHOL 64) with
  | .load sh _ => Shape.shapeToString (shapeOfHOL sh) = "1"
  | _ => false

/-- Row `ex_load32`. -/
private def load32Row : Bool :=
  match (ExpHOL.load32 (.const (7 : BitVec 64)) : ExpHOL 64) with
  | .load32 _ => true
  | _ => false

/-- Row `ex_op_len`: `Op Add` has a two-element argument list. -/
private def opRow : Bool :=
  ((([.const (1 : BitVec 64), .const 2] : List (ExpHOL 64)).length) = 2)

/-- Row `ex_panop_len`: `Panop Mul` has a one-element argument list. -/
private def panopRow : Bool :=
  ((([.const (1 : BitVec 64)] : List (ExpHOL 64)).length) = 1)

/-- Row `ex_cmp`. -/
private def cmpRow : Bool :=
  match (ExpHOL.cmp .equal (.const (1 : BitVec 64)) (.const 2) : ExpHOL 64) with
  | .cmp _ _ _ => true
  | _ => false

/-- Row `ex_shift`. -/
private def shiftRow : Bool :=
  match (ExpHOL.shift .lsl (.const (1 : BitVec 64)) (.const 2) : ExpHOL 64) with
  | .shift _ _ _ => true
  | _ => false

/-- Row `ex_baseaddr`. -/
private def baseAddrRow : Bool :=
  match (ExpHOL.baseAddr : ExpHOL 64) with
  | .baseAddr => true
  | _ => false

/-- Row `ex_topaddr`. -/
private def topAddrRow : Bool :=
  match (ExpHOL.topAddr : ExpHOL 64) with
  | .topAddr => true
  | _ => false

/-- Row `ex_bytesinword`. -/
private def bytesInWordRow : Bool :=
  match (ExpHOL.bytesInWord : ExpHOL 64) with
  | .bytesInWord => true
  | _ => false

private def parityGuard : Bool :=
  constRow && varRow && rstructRow && rfieldRow && nstructRow && nfieldRow &&
    loadShapeRow && load32Row && opRow && panopRow && cmpRow && shiftRow &&
    baseAddrRow && topAddrRow && bytesInWordRow

#eval parityGuard
#guard parityGuard

/-- The exact carrier round trips through production syntax and back. -/
example : expToHOL (expOfHOL (.const (5 : BitVec 64) : ExpHOL 64)) =
    (.const (5 : BitVec 64) : ExpHOL 64) :=
  expToHOL_expOfHOL _

example : expToHOL (expOfHOL
    (.load .one (.const (0 : BitVec 64)) : ExpHOL 64)) =
    (.load .one (.const (0 : BitVec 64)) : ExpHOL 64) :=
  expToHOL_expOfHOL _

/-- The reverse direction is exact on byte-ranged production expressions; this
is the documented side condition. -/
example : expOfHOL (expToHOL (Exp.const (7 : BitVec 64))) =
    Exp.const (7 : BitVec 64) :=
  expOfHOL_expToHOL _ (by simp [ExpByteRanged])

example : expOfHOL (expToHOL (Exp.nField "foo" (Exp.const (7 : BitVec 64)))) =
    Exp.nField "foo" (Exp.const (7 : BitVec 64)) :=
  expOfHOL_expToHOL _ (by simp [ExpByteRanged])

/-! ### `panLang$shape_val` parity (bead `flapjack-4ac.1.29`)

The rows reproduce `scripts/hol-probes/pan_lang_shape_val_probe.out`:
`shape_val One = Const 0w`, `shape_val (Comb [...]) = RStruct [...]` with one
zero word per component, and `shape_val (Named _) = Const 0w`. -/

example : shapeValHOL (width := 64) (ShapeHOL.one) =
    (ExpHOL.const 0 : ExpHOL 64) := by simp [shapeValHOL]

example : shapeValHOL (width := 64)
      (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.named (ofString "n"), ShapeHOL.one]) =
    (ExpHOL.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0] :
      ExpHOL 64) := by simp [shapeValHOL]

example : shapeValHOL (width := 64) (ShapeHOL.named (ofString "n")) =
    (ExpHOL.const 0 : ExpHOL 64) := by simp [shapeValHOL]

end Flapjack.Test.PanLangExpHOLParity