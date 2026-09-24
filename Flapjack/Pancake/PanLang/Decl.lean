/-
Exact HOL `panLang$fun_decl`, `panLang$decl`, and `panLang$struct_info` carriers
over the faithful `MlString` name carrier (bead flapjack-pxn.18.3.5.8.4).

Source: `cakeml/pancake/panLangScript.sml:102-122`

```
Datatype:
  fun_decl =
  <| name : mlstring; inline : bool; export : bool
   ; params : (varname # shape) list; body : 'a prog; return : shape |>
End
Datatype:
  decl = Function ('a fun_decl) | Decl shape mlstring ('a exp)
       | ExnDecl eid shape | Name stcname ((fldname # shape) list)
End
Datatype:
  struct_info = <| fields : (fldname # shape) list; size : num |>
End
```

where `varname`/`fldname`/`stcname`/`eid` are aliases for `mlstring`
(`panLangScript.sml:23-31`).  The production `Flapjack.FunDecl α`,
`Flapjack.Decl α`, and `Flapjack.StructInfoHOL` use Lean `String` identifiers,
generic `Exp α`/`Prog α`, and monomorphic `Shape`; they are untagged.  The
carriers below are indexed by the HOL word dimension and use `MlS`
(`Flapjack.Basis.Pure.MlString.MlString`) for every name, so they are exact
word-indexed ports.  Lean cannot name the `return` field literally (keyword), so
the field is `returnShape`, matching production; `export` is spelled `exported`.

The codecs `*ToHOL`/`*OfHOL` bridge to the production carriers.  The total
roundtrip `*ToHOL (*OfHOL x) = x` is kernel-checked below.
-/
import Flapjack.Pancake.PanLang.Prog

namespace Flapjack.Pancake.PanLang

open Flapjack.Basis.Pure.MlString

/-- Exact port of HOL `panLang$fun_decl` (`panLangScript.sml:102-109`):
`name : mlstring`, `inline`/`export : bool`, `params : (varname # shape) list`,
`body : 'a prog`, `return : shape`.  `return` is spelled `returnShape` (Lean
keyword) and `export` is `exported`. -/
@[hol "cakeml/pancake/panLangScript.sml" "fun_decl"]
structure FunDeclHOL (width : Nat) [NeZero width] where
  name : MlS
  inline : Bool
  exported : Bool
  params : List (MlS × ShapeHOL)
  body : ProgHOL width
  returnShape : ShapeHOL
  deriving Repr

/-- Exact port of HOL `panLang$decl` (`panLangScript.sml:111-116`):
`Function ('a fun_decl) | Decl shape mlstring ('a exp) | ExnDecl eid shape | Name
stcname ((fldname # shape) list)`, with every identifier an `mlstring` and the
exp/prog payloads word-indexed. -/
@[hol "cakeml/pancake/panLangScript.sml" "decl"]
inductive DeclHOL (width : Nat) [NeZero width] where
  | function (declaration : FunDeclHOL width)
  | decl (shape : ShapeHOL) (name : MlS) (value : ExpHOL width)
  | exnDecl (exceptionName : MlS) (shape : ShapeHOL)
  | name (struct : MlS) (fields : List (MlS × ShapeHOL))
  deriving Repr

/-- Exact port of HOL `panLang$struct_info` (`panLangScript.sml:118-122`):
`fields : (fldname # shape) list`, `size : num`, with `fldname` an `mlstring`. -/
@[hol "cakeml/pancake/panLangScript.sml" "struct_info"]
structure StructInfoHOLExact where
  fields : List (MlS × ShapeHOL)
  size : Nat
  deriving Repr

/-! ### Codecs to the production carriers -/

/-- `(fldname # shape)` pair, HOL to production. -/
def paramOfHOL (p : MlS × ShapeHOL) : String × Flapjack.Shape :=
  (toStringOfBytes p.1, shapeOfHOL p.2)

/-- `(fldname # shape)` pair, production to HOL. -/
def paramToHOL (p : String × Flapjack.Shape) : MlS × ShapeHOL :=
  (ofString p.1, shapeToHOL p.2)

@[simp] theorem paramToHOL_paramOfHOL (p : MlS × ShapeHOL) :
    paramToHOL (paramOfHOL p) = p := by
  obtain ⟨name, shape⟩ := p
  simp [paramToHOL, paramOfHOL, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]

@[simp] theorem listParamToHOL_paramOfHOL (l : List (MlS × ShapeHOL)) :
    l.map (paramToHOL ∘ paramOfHOL) = l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, Function.comp_apply, paramToHOL_paramOfHOL, ih]

/-- Production carrier of `fun_decl` (`String` names, monomorphic `Shape`). -/
abbrev FunDeclOf (width : Nat) := Flapjack.FunDecl (BitVec width)

/-- HOL `fun_decl` to the production carrier. -/
def funDeclOfHOL {width : Nat} [NeZero width] (d : FunDeclHOL width) : FunDeclOf width :=
  { name := toStringOfBytes d.name
    inline := d.inline
    exported := d.exported
    params := d.params.map paramOfHOL
    body := progOfHOL d.body
    returnShape := shapeOfHOL d.returnShape }

/-- Production carrier of `fun_decl` to the exact HOL carrier. -/
def funDeclToHOL {width : Nat} [NeZero width] (d : FunDeclOf width) : FunDeclHOL width :=
  { name := ofString d.name
    inline := d.inline
    exported := d.exported
    params := d.params.map paramToHOL
    body := progToHOL d.body
    returnShape := shapeToHOL d.returnShape }

@[simp] theorem funDeclToHOL_funDeclOfHOL {width : Nat} [NeZero width]
    (d : FunDeclHOL width) : funDeclToHOL (funDeclOfHOL d) = d := by
  obtain ⟨name, inline, exported, params, body, returnShape⟩ := d
  simp [funDeclToHOL, funDeclOfHOL, listParamToHOL_paramOfHOL,
    Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes, progToHOL_progOfHOL,
    shapeToHOL_shapeOfHOL]

/-- HOL `decl` to the production carrier. -/
def declOfHOL {width : Nat} [NeZero width] : DeclHOL width → Flapjack.Decl (BitVec width)
  | .function d => .function (funDeclOfHOL d)
  | .decl shape name value => .decl (shapeOfHOL shape) (toStringOfBytes name) (expOfHOL value)
  | .exnDecl exceptionName shape => .exnDecl (toStringOfBytes exceptionName) (shapeOfHOL shape)
  | .name struct fields => .name (toStringOfBytes struct) (fields.map paramOfHOL)

/-- Production carrier of `decl` to the exact HOL carrier. -/
def declToHOL {width : Nat} [NeZero width] : Flapjack.Decl (BitVec width) → DeclHOL width
  | .function d => .function (funDeclToHOL d)
  | .decl shape name value => .decl (shapeToHOL shape) (ofString name) (expToHOL value)
  | .exnDecl exceptionName shape => .exnDecl (ofString exceptionName) (shapeToHOL shape)
  | .name struct fields => .name (ofString struct) (fields.map paramToHOL)

@[simp] theorem declToHOL_declOfHOL {width : Nat} [NeZero width]
    (d : DeclHOL width) : declToHOL (declOfHOL d) = d := by
  cases d <;>
    simp [declToHOL, declOfHOL, funDeclToHOL_funDeclOfHOL, listParamToHOL_paramOfHOL,
      expToHOL_expOfHOL, shapeToHOL_shapeOfHOL, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]

/-- HOL `struct_info` to the production-shaped carrier. -/
def structInfoOfHOL (d : StructInfoHOLExact) : Flapjack.StructInfoHOL :=
  { fields := d.fields.map paramOfHOL, size := d.size }

/-- Production-shaped carrier to the exact HOL `struct_info`. -/
def structInfoToHOL (d : Flapjack.StructInfoHOL) : StructInfoHOLExact :=
  { fields := d.fields.map paramToHOL, size := d.size }

@[simp] theorem structInfoToHOL_structInfoOfHOL (d : StructInfoHOLExact) :
    structInfoToHOL (structInfoOfHOL d) = d := by
  obtain ⟨fields, size⟩ := d
  simp [structInfoToHOL, structInfoOfHOL, listParamToHOL_paramOfHOL]

end Flapjack.Pancake.PanLang