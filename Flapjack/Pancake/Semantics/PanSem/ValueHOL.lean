import Flapjack.HolRef
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.PanLang.Shape

/-!
# Exact `panSem$v` over the faithful `mlstring`/`word_lab` carriers

HOL `panSem$v` (`cakeml/pancake/semantics/panSemScript.sml:22`) is

```
v = Val ('a word_lab) | RStruct (v list) | NStruct stcname ((fldname # v) list)
```

where `stcname = fldname = mlstring` (`panLangScript.sml:23-24`) and
`word_lab = Word ('a word)` (`panSemScript.sml:17`).

The executable `Flapjack.PanValue` types the `NStruct` name and field names by
Lean `String` and stores the word payload `α` directly in `.word`, so its
`@[hol ... "v"]` tag is not exact (withdrawn; `flapjack-0lj`).  `ValueHOL` below
is the exact counterpart: constructor arities `1/1/2`, the `Val` payload is the
faithful `HolWordLab`, and the `NStruct` key/field names are `mlstring`
(`MlStringHOL`).

`flattenHOL` and `panPrimopHOLExact` are the exact `flatten_def`
(`panSemScript.sml:388`) and `pan_primop_def` (`:196`) ports over `ValueHOL`,
with direct original-HOL oracle rows in
`scripts/hol-probes/pan_flatten_probe.out` and
`scripts/hol-probes/pan_sem_pan_primop_probe.out` reproduced by
`Flapjack/Test/PanSemValueHOLParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- The faithful Cake `mlstring` carrier, local abbreviation. -/
abbrev MlStringHOL := Flapjack.Basis.Pure.MlString.MlString

/-- Exact port of HOL `panSem$v` (`cakeml/pancake/semantics/panSemScript.sml:22`).

    Constructor arities `1/1/2` and field types
    `HolWordLab width`, `List (ValueHOL width)`, `List (MlStringHOL × ValueHOL width)`
    match the HOL datatype (`Val ('a word_lab)`, `RStruct (v list)`,
    `NStruct stcname ((fldname # v) list)`).  Like production `PanValue` it
    derives only `Repr`.  The `[NeZero width]` binder matches HOL's positive
    `dimindex`; the payload `HolWordLab` is the (tag-withheld) generic carrier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "v"]
inductive ValueHOL (width : Nat) [NeZero width] where
  | val (value : HolWordLab width)
  | rStruct (fields : List (ValueHOL width))
  | nStruct (name : MlStringHOL) (fields : List (MlStringHOL × ValueHOL width))
  deriving Repr

/-- Exact port of HOL `flatten_def` (`cakeml/pancake/semantics/panSemScript.sml:388`):
    `flatten (Val w) = [w]`, `flatten (RStruct vs) = FLAT (MAP flatten vs)`,
    `flatten (NStruct nm flds) = FLAT (MAP flatten (MAP SND flds))`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "flatten_def"]
def flattenHOL {width : Nat} [NeZero width] : ValueHOL width → List (HolWordLab width)
  | .val value => [value]
  | .rStruct fields => (fields.map flattenHOL).flatten
  | .nStruct _ fields => (fields.map (fun pair => flattenHOL pair.2)).flatten
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | (rename_i hmem
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)
    | (rename_i hmem
       have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
       have hlt := List.sizeOf_lt_of_mem hmem
       omega)

/-- Exact port of HOL `pan_primop_def` (`cakeml/pancake/semantics/panSemScript.sml:196`):
    `pan_primop AddCarry args = if LENGTH args = 3 /\ EVERY isValWord args then`
    `let l = theValWord (EL 0 args); r = theValWord (EL 1 args);`
    `ci = theValWord (EL 2 args); (res, co) = word_add_carry l r ci in`
    `SOME (RStruct [ValWord res; ValWord co]) else NONE`.

    The three-element `EVERY isValWord` side condition renders as the exact
    `.val (.word _)` triple pattern: `isValWord` is automatic for the
    `word_lab` payload, so the only surviving constraint is the arity. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "pan_primop_def"]
def panPrimopHOLExact {width : Nat} [NeZero width] :
    PrimOp → List (ValueHOL width) → Option (ValueHOL width)
  | .addCarry, [.val (.word left), .val (.word right), .val (.word carry)] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some (.rStruct [.val (.word result), .val (.word overflow)])
  | _, _ => none

/- HOL `panSemScript.sml:80-84` `shape_of_def` is total over `v`:
   `shape_of (ValWord _) = One`, `shape_of (RStruct vs) = Comb (MAP shape_of vs)`,
   `shape_of (NStruct nm _) = Named nm`.  Stated over the exact `ValueHOL`/`ShapeHOL`
   carriers; `ValWord w` is `Val (Word w)`, so the `val` case ignores the word_lab
   payload. -/
mutual
  @[hol "cakeml/pancake/semantics/panSemScript.sml" "shape_of_def"]
  def shapeOfHOL {width : Nat} [NeZero width] : ValueHOL width → ShapeHOL
    | .val _ => .one
    | .rStruct fields => .comb (shapeOfsHOL fields)
    | .nStruct name _ => .named name
  def shapeOfsHOL {width : Nat} [NeZero width] : List (ValueHOL width) → List ShapeHOL
    | [] => []
    | value :: values => shapeOfHOL value :: shapeOfsHOL values
end

@[simp] theorem shapeOfHOL_val {width : Nat} [NeZero width] (value : HolWordLab width) :
    shapeOfHOL (.val value : ValueHOL width) = .one := by
  simp only [shapeOfHOL]

@[simp] theorem shapeOfHOL_rStruct {width : Nat} [NeZero width]
    (fields : List (ValueHOL width)) :
    shapeOfHOL (.rStruct fields : ValueHOL width) = .comb (shapeOfsHOL fields) := by
  simp only [shapeOfHOL]

@[simp] theorem shapeOfHOL_nStruct {width : Nat} [NeZero width]
    (name : MlStringHOL) (fields : List (MlStringHOL × ValueHOL width)) :
    shapeOfHOL (.nStruct name fields : ValueHOL width) = .named name := by
  simp only [shapeOfHOL]

@[simp] theorem shapeOfsHOL_nil {width : Nat} [NeZero width] :
    shapeOfsHOL ([] : List (ValueHOL width)) = [] := by
  simp only [shapeOfsHOL]

@[simp] theorem shapeOfsHOL_cons {width : Nat} [NeZero width]
    (value : ValueHOL width) (values : List (ValueHOL width)) :
    shapeOfsHOL (value :: values) = shapeOfHOL value :: shapeOfsHOL values := by
  simp only [shapeOfsHOL]

end Flapjack
