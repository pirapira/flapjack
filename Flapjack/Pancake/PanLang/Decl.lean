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

/-- Exact port of HOL `panLang$functions` (`panLangScript.sml:319-326`):
`functions` projects the top-level function declarations of a program in source
order, returning `(name, params, body, return)` for each `Function` and dropping
`Decl`/`ExnDecl`/`Name` entries.  Names use `MlS`, shapes use `ShapeHOL`, and
bodies use the word-indexed `ProgHOL width`, so this is an exact word-indexed
port (the production `functionEntries`/`functions` use Lean `String` and generic
`Prog α`). -/
@[hol "cakeml/pancake/panLangScript.sml" "functions_def"]
def functionsHOL {width : Nat} [NeZero width] :
    List (DeclHOL width) →
      List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, declaration.params, declaration.body,
        declaration.returnShape) :: functionsHOL declarations
  | .decl _ _ _ :: declarations => functionsHOL declarations
  | .exnDecl _ _ :: declarations => functionsHOL declarations
  | .name _ _ :: declarations => functionsHOL declarations

/-- Exact port of HOL `panLang$is_decl` (`panLangScript.sml:234-237`):
`is_decl (Decl sh v e) = T`, `is_decl _ = F`.  The argument carrier
`DeclHOL width` is the reviewed word-indexed rendering of HOL's polymorphic
`'a decl` (see the `decl` tag above), so the body transfers clause for
clause. -/
@[hol "cakeml/pancake/panLangScript.sml" "is_decl_def"]
def isDeclHOL {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .decl _ _ _ => true
  | _ => false

/-- Exact port of HOL `panLang$is_exn_decl` (`panLangScript.sml:239-242`):
true only for `ExnDecl`. -/
@[hol "cakeml/pancake/panLangScript.sml" "is_exn_decl_def"]
def isExnDeclHOL {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .exnDecl _ _ => true
  | _ => false

/-- Exact port of HOL `panLang$is_function` (`panLangScript.sml:314-317`):
`is_function (Function _) = T`, `is_function _ = F`, over the same reviewed
`DeclHOL width` carrier. -/
@[hol "cakeml/pancake/panLangScript.sml" "is_function_def"]
def isFunctionHOL {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function _ => true
  | _ => false

/-- Exact port of HOL `panLang$exceptions` (`panLangScript.sml:328-333`):
projects the top-level exception declarations of a program in source order,
returning `(eid, shape)` for each `ExnDecl` and dropping
`Function`/`Decl`/`Name` entries.  The exception id is an `MlS` and the shape
uses `ShapeHOL`, so this is an exact word-indexed port (the production
`exceptionEntries` uses Lean `String` and monomorphic `Shape`).

Executable-path disposition (bead `flapjack-4ac.1.44.1`): the compiled RISC-V
pipeline extracts exception ids through `crepGetEidsFromDecls`
(`Flapjack/Pipeline.lean:66`, used by `pipelineCrepeContext` /
`pipelineCrepeCompileContext` at `:315` / `:324`), which numbers `.exnDecl`
entries directly and calls neither `exceptionEntries` nor `exceptionsHOL`.
Production `exceptionEntries` is executed only by the untagged mirror
`panToCrepGetEidsFromDeclsHOL`
(`Flapjack/Pancake/PanToCrep/Compile.lean:1131`) inside `compileToCrepHOL`,
which has no executable caller (the run path uses `compileToCrep` plus
`panToCrepCompileInlTop`; `compileProgToCrepHOL` appears only in proofs and
tests). Routing the executable extraction through this reviewed predicate
additionally needs a total checked codec `declOfHOL ∘ declToHOL = id`, which
currently holds only under byte-ranged hypotheses (`declOfHOL_declToHOL`), so
the faithful executable route depends on the MlString/`ShapeHOL` carrier work
tracked by `flapjack-pxn.18.3.5.8`. The proof-side bridge
`exceptionsHOL_map_paramOfHOL` already connects the reviewed predicate to the
production analogue. -/
@[hol "cakeml/pancake/panLangScript.sml" "exceptions_def"]
def exceptionsHOL {width : Nat} [NeZero width] :
    List (DeclHOL width) → List (MlS × ShapeHOL)
  | [] => []
  | .function _ :: declarations => exceptionsHOL declarations
  | .decl _ _ _ :: declarations => exceptionsHOL declarations
  | .exnDecl exceptionName shape :: declarations =>
      (exceptionName, shape) :: exceptionsHOL declarations
  | .name _ _ :: declarations => exceptionsHOL declarations

/-- The exact `exceptionsHOL` projects exactly the same `(name, shape)` pairs as
the production `exceptionEntries` after the carrier bridge `paramOfHOL` /
`declOfHOL`. -/
@[simp] theorem exceptionsHOL_map_paramOfHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    (exceptionsHOL declarations).map paramOfHOL =
      exceptionEntries (declarations.map declOfHOL) := by
  induction declarations with
  | nil => simp [exceptionsHOL, exceptionEntries]
  | cons d ds ih =>
    cases d <;> simp [exceptionsHOL, exceptionEntries, declOfHOL, paramOfHOL, ih]

/-- Componentwise production carrier of one `functionsHOL` entry: the `MlS`
name and shape/`ProgHOL` payloads are mapped through the reviewed codecs
`toStringOfBytes`, `paramOfHOL`, `progOfHOL` and `shapeOfHOL`. -/
def funEntryOfHOL {width : Nat} [NeZero width]
    (entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    FunName × List (VarName × Shape) × Prog (BitVec width) × Shape :=
  (toStringOfBytes entry.1, entry.2.1.map paramOfHOL,
    progOfHOL entry.2.2.1, shapeOfHOL entry.2.2.2)

/-- The exact `functionsHOL` projects exactly the same `Function` entries as the
production `functionEntries` after the carrier bridge. Direct executable routing
of `functionEntries` to `functionsHOL` is unavailable because production is
polymorphic over `Decl α` with `String` names while the tagged `functionsHOL` is
over the word-indexed `DeclHOL` with `MlString`/`ShapeHOL`/`ProgHOL` carriers;
this checked bridge is the relation between them (bead flapjack-ni1.2). -/
@[simp] theorem functionsHOL_map_funEntryOfHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    (functionsHOL declarations).map funEntryOfHOL =
      functionEntries (declarations.map declOfHOL) := by
  induction declarations with
  | nil => simp [functionsHOL, functionEntries]
  | cons d ds ih =>
    cases d <;>
      simp [functionsHOL, functionEntries, declOfHOL, funDeclOfHOL, funEntryOfHOL, ih]

/-! ### Reverse (byte-ranged) roundtrips to production

The forward codecs above recover an exact HOL carrier from any production
value. The reverse direction `production -> HOL -> production` is exact only
for values whose names fit in HOL's 256-character universe (`NameRanged`) and
whose embedded shapes/exps/progs are themselves byte-ranged; those predicates
mirror the side conditions used by `shapeOfHOL_shapeToHOL`,
`expOfHOL_expToHOL` and `progOfHOL_progToHOL`. -/

/-- A production `(fldname # shape)` pair that survives the HOL roundtrip. -/
def ParamByteRanged (p : String × Flapjack.Shape) : Prop :=
  NameRanged p.1 ∧ ShapeByteRanged p.2

/-- Every pair of a production association list survives the HOL roundtrip. -/
def ListParamByteRanged (l : List (String × Flapjack.Shape)) : Prop :=
  ∀ p ∈ l, ParamByteRanged p

/-- A production `fun_decl` that survives the HOL roundtrip. -/
def FunDeclByteRanged {width : Nat} (d : FunDeclOf width) : Prop :=
  NameRanged d.name ∧ ListParamByteRanged d.params ∧ ProgByteRanged d.body ∧
    ShapeByteRanged d.returnShape

/-- A production `decl` that survives the HOL roundtrip. -/
def DeclByteRanged {width : Nat} : Flapjack.Decl (BitVec width) → Prop
  | .function d => FunDeclByteRanged d
  | .decl shape name value => ShapeByteRanged shape ∧ NameRanged name ∧ ExpByteRanged value
  | .exnDecl exceptionName shape => NameRanged exceptionName ∧ ShapeByteRanged shape
  | .name struct fields => NameRanged struct ∧ ListParamByteRanged fields

/-- A production `struct_info` that survives the HOL roundtrip. -/
def StructInfoByteRanged (d : Flapjack.StructInfoHOL) : Prop :=
  ListParamByteRanged d.fields

/-- Reverse codec on a byte-ranged pair. -/
@[simp] theorem paramOfHOL_paramToHOL (p : String × Flapjack.Shape)
    (h : ParamByteRanged p) : paramOfHOL (paramToHOL p) = p := by
  obtain ⟨name, shape⟩ := p
  obtain ⟨hname, hshape⟩ := h
  simp [paramOfHOL, paramToHOL,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
    shapeOfHOL_shapeToHOL shape hshape]

/-- Reverse codec on a byte-ranged association list. -/
theorem listParamOfHOL_paramToHOL (l : List (String × Flapjack.Shape))
    (h : ListParamByteRanged l) : l.map (paramOfHOL ∘ paramToHOL) = l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [List.map_cons, Function.comp_apply]
    rw [paramOfHOL_paramToHOL p (h p (by simp))]
    rw [ih (fun q hq => h q (by simp [hq]))]

/-- Reverse roundtrip for production `fun_decl`. -/
@[simp] theorem funDeclOfHOL_funDeclToHOL {width : Nat} [NeZero width]
    (d : FunDeclOf width) (h : FunDeclByteRanged d) :
    funDeclOfHOL (funDeclToHOL d) = d := by
  obtain ⟨name, inline, exported, params, body, returnShape⟩ := d
  simp only [FunDeclByteRanged] at h
  obtain ⟨hname, hparams, hbody, hret⟩ := h
  simp [funDeclToHOL, funDeclOfHOL,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
    listParamOfHOL_paramToHOL params hparams, progOfHOL_progToHOL body hbody,
    shapeOfHOL_shapeToHOL returnShape hret]

/-- Reverse roundtrip for production `decl`. -/
@[simp] theorem declOfHOL_declToHOL {width : Nat} [NeZero width]
    (d : Flapjack.Decl (BitVec width)) (h : DeclByteRanged d) :
    declOfHOL (declToHOL d) = d := by
  cases d with
  | function fd =>
    simp only [DeclByteRanged] at h
    simp [declToHOL, declOfHOL, funDeclOfHOL_funDeclToHOL fd h]
  | decl shape name value =>
    simp only [DeclByteRanged] at h
    obtain ⟨hshape, hname, hvalue⟩ := h
    simp [declToHOL, declOfHOL, shapeOfHOL_shapeToHOL shape hshape,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
      expOfHOL_expToHOL value hvalue]
  | exnDecl exceptionName shape =>
    simp only [DeclByteRanged] at h
    obtain ⟨hname, hshape⟩ := h
    simp [declToHOL, declOfHOL,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName hname,
      shapeOfHOL_shapeToHOL shape hshape]
  | name struct fields =>
    simp only [DeclByteRanged] at h
    obtain ⟨hstruct, hfields⟩ := h
    simp [declToHOL, declOfHOL,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes struct hstruct,
      listParamOfHOL_paramToHOL fields hfields]

/-- Reverse roundtrip for production `struct_info`. -/
@[simp] theorem structInfoOfHOL_structInfoToHOL (d : Flapjack.StructInfoHOL)
    (h : StructInfoByteRanged d) : structInfoOfHOL (structInfoToHOL d) = d := by
  obtain ⟨fields, size⟩ := d
  simp only [StructInfoByteRanged] at h
  simp [structInfoToHOL, structInfoOfHOL, listParamOfHOL_paramToHOL fields h]

/-! ### Pass-boundary bridge: the struct context

`panLangScript.sml`'s compiler passes range `is_wf_shape` over a struct context
`(stcname # struct_info) list`. The exact MlString-keyed context is bridged to
the production `StructContextHOL` here, so an exact pass input is recoverable
from its production image on byte-ranged contexts. -/

/-- Exact MlString-keyed struct context. -/
abbrev StructContextExact := List (MlS × StructInfoHOLExact)

/-- Exact struct context to the production `StructContextHOL`. -/
def structContextOfHOL (c : StructContextExact) : Flapjack.StructContextHOL :=
  c.map (fun p => (toStringOfBytes p.1, structInfoOfHOL p.2))

/-- Production `StructContextHOL` to the exact MlString-keyed context. -/
def structContextToHOL (c : Flapjack.StructContextHOL) : StructContextExact :=
  c.map (fun p => (ofString p.1, structInfoToHOL p.2))

/-- Production struct context that survives the HOL roundtrip. -/
def StructContextByteRanged (c : Flapjack.StructContextHOL) : Prop :=
  ∀ p ∈ c, NameRanged p.1 ∧ StructInfoByteRanged p.2

@[simp] theorem structContextToHOL_structContextOfHOL (c : StructContextExact) :
    structContextToHOL (structContextOfHOL c) = c := by
  unfold structContextToHOL structContextOfHOL
  rw [List.map_map]
  induction c with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨name, info⟩ := p
    simp only [List.map_cons, Function.comp_apply,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
      structInfoToHOL_structInfoOfHOL, ih]

@[simp] theorem structContextOfHOL_structContextToHOL (c : Flapjack.StructContextHOL)
    (h : StructContextByteRanged c) : structContextOfHOL (structContextToHOL c) = c := by
  unfold structContextOfHOL structContextToHOL
  rw [List.map_map]
  induction c with
  | nil => rfl
  | cons p t ih =>
    have hp : NameRanged p.1 ∧ StructInfoByteRanged p.2 := h p (by simp)
    obtain ⟨name, info⟩ := p
    obtain ⟨hname, hinfo⟩ := hp
    have ht : StructContextByteRanged t := fun q hq => h q (by simp [hq])
    simp only [List.map_cons, Function.comp_apply,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
      structInfoOfHOL_structInfoToHOL info hinfo, ih ht]


/-- HOL `ALOOKUP` over the exact MlString-keyed structure context
(`panLangScript.sml:164-171` uses `ALOOKUP ctxt name`): first name match. -/
def structContextLookupHOL (name : MlS) : StructContextExact → Option StructInfoHOLExact
  | [] => none
  | (candidate, info) :: rest =>
      if name = candidate then some info else structContextLookupHOL name rest

/-! Exact port of HOL `panLang$size_of_sh_with_ctxt`
(`cakeml/pancake/panLangScript.sml:164-171`): `One` is `1`, `Comb` sums the
field sizes, and `Named name` is the size of the first matching structure, or
`1` when absent (HOL's "should not happen").  The context is the exact
MlString-keyed `StructContextExact` and the shapes are `ShapeHOL`. -/
mutual
  @[hol "cakeml/pancake/panLangScript.sml" "size_of_sh_with_ctxt_def"]
  def sizeOfShapeWithContextHOL (context : StructContextExact) : ShapeHOL → Nat
    | .one => 1
    | .comb shapes => sizeOfShapesWithContextHOL context shapes
    | .named name =>
        match structContextLookupHOL name context with
        | some info => info.size
        | none => 1

  /- Sum of `sizeOfShapeWithContextHOL` over a list of shapes (HOL
  `SUM (MAP (size_of_sh_with_ctxt ctxt) shapes)`). -/
  def sizeOfShapesWithContextHOL (context : StructContextExact) : List ShapeHOL → Nat
    | [] => 0
    | shape :: rest =>
        sizeOfShapeWithContextHOL context shape + sizeOfShapesWithContextHOL context rest
end

@[simp] theorem structContextLookupHOL_nil (name : MlS) :
    structContextLookupHOL name ([] : StructContextExact) = none := rfl

@[simp] theorem structContextLookupHOL_cons (name candidate : MlS)
    (info : StructInfoHOLExact) (rest : StructContextExact) :
    structContextLookupHOL name ((candidate, info) :: rest) =
      (if name = candidate then some info else structContextLookupHOL name rest) := rfl

/-- `ALOOKUP` of an appended context is the first match in the prefix, or else
    the lookup in the suffix (HOL `ALOOKUP_APPEND`). -/
theorem structContextLookupHOL_append (name : MlS) (first second : StructContextExact) :
    structContextLookupHOL name (first ++ second) =
      (match structContextLookupHOL name first with
        | some info => some info
        | none => structContextLookupHOL name second) := by
  induction first with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨candidate, info⟩ := pair
      by_cases h : name = candidate
      · simp [h]
      · simp [h, ih]

@[simp] theorem sizeOfShapeWithContextHOL_one (context : StructContextExact) :
    sizeOfShapeWithContextHOL context .one = 1 := rfl

@[simp] theorem sizeOfShapeWithContextHOL_comb (context : StructContextExact)
    (shapes : List ShapeHOL) :
    sizeOfShapeWithContextHOL context (.comb shapes) =
      sizeOfShapesWithContextHOL context shapes := by
  simp only [sizeOfShapeWithContextHOL]

@[simp] theorem sizeOfShapeWithContextHOL_named_hit (context : StructContextExact)
    (name : MlS) (info : StructInfoHOLExact)
    (h : structContextLookupHOL name context = some info) :
    sizeOfShapeWithContextHOL context (.named name) = info.size := by
  simp only [sizeOfShapeWithContextHOL, h]

@[simp] theorem sizeOfShapeWithContextHOL_named_miss (context : StructContextExact)
    (name : MlS) (h : structContextLookupHOL name context = none) :
    sizeOfShapeWithContextHOL context (.named name) = 1 := by
  simp only [sizeOfShapeWithContextHOL, h]

@[simp] theorem sizeOfShapesWithContextHOL_nil (context : StructContextExact) :
    sizeOfShapesWithContextHOL context ([] : List ShapeHOL) = 0 := rfl

@[simp] theorem sizeOfShapesWithContextHOL_cons (context : StructContextExact)
    (shape : ShapeHOL) (rest : List ShapeHOL) :
    sizeOfShapesWithContextHOL context (shape :: rest) =
      sizeOfShapeWithContextHOL context shape + sizeOfShapesWithContextHOL context rest := by
  simp only [sizeOfShapesWithContextHOL]

/-! Exact port of HOL `panLang$is_wf_shape`/`is_wf_flds`/`is_wf_ctxt`
(`cakeml/pancake/panLangScript.sml:139-163`) over the exact MlString-keyed
`ShapeHOL`/`StructContextExact` carriers.  `Named nm` is well formed exactly
when `nm` is present in the context (`ALOOKUP ctxt nm = SOME _`); the context
predicate additionally requires that no earlier structure shares a name and
that every structure's fields are well formed. -/
mutual
  @[hol "cakeml/pancake/panLangScript.sml" "is_wf_shape_def"]
  def isWfShapeExactHOL (context : StructContextExact) : ShapeHOL → Bool
    | .one => true
    | .comb shapes => isWfShapesExactHOL context shapes
    | .named name => (structContextLookupHOL name context).isSome

  /- `EVERY (is_wf_shape ctxt) shs` over a shape list. -/
  def isWfShapesExactHOL (context : StructContextExact) : List ShapeHOL → Bool
    | [] => true
    | shape :: rest => isWfShapeExactHOL context shape && isWfShapesExactHOL context rest

  @[hol "cakeml/pancake/panLangScript.sml" "is_wf_flds_def"]
  def isWfFldsExactHOL (context : StructContextExact) : List (MlS × ShapeHOL) → Bool
    | [] => true
    | (_, shape) :: rest => isWfShapeExactHOL context shape && isWfFldsExactHOL context rest

  @[hol "cakeml/pancake/panLangScript.sml" "is_wf_ctxt_def"]
  def isWfCtxtExactHOL : StructContextExact → Bool
    | [] => true
    | (name, info) :: rest =>
        (structContextLookupHOL name rest).isNone &&
          isWfFldsExactHOL rest info.fields && isWfCtxtExactHOL rest
end

@[simp] theorem isWfShapeExactHOL_one (context : StructContextExact) :
    isWfShapeExactHOL context .one = true := rfl

@[simp] theorem isWfShapeExactHOL_comb (context : StructContextExact)
    (shapes : List ShapeHOL) :
    isWfShapeExactHOL context (.comb shapes) = isWfShapesExactHOL context shapes := by
  simp only [isWfShapeExactHOL]

@[simp] theorem isWfShapeExactHOL_named (context : StructContextExact) (name : MlS) :
    isWfShapeExactHOL context (.named name) = (structContextLookupHOL name context).isSome := by
  simp only [isWfShapeExactHOL]

@[simp] theorem isWfShapesExactHOL_nil (context : StructContextExact) :
    isWfShapesExactHOL context ([] : List ShapeHOL) = true := rfl

@[simp] theorem isWfShapesExactHOL_cons (context : StructContextExact)
    (shape : ShapeHOL) (rest : List ShapeHOL) :
    isWfShapesExactHOL context (shape :: rest) =
      (isWfShapeExactHOL context shape && isWfShapesExactHOL context rest) := by
  simp only [isWfShapesExactHOL]

@[simp] theorem isWfFldsExactHOL_nil (context : StructContextExact) :
    isWfFldsExactHOL context ([] : List (MlS × ShapeHOL)) = true := rfl

@[simp] theorem isWfFldsExactHOL_cons (context : StructContextExact)
    (name : MlS) (shape : ShapeHOL) (rest : List (MlS × ShapeHOL)) :
    isWfFldsExactHOL context ((name, shape) :: rest) =
      (isWfShapeExactHOL context shape && isWfFldsExactHOL context rest) := by
  simp only [isWfFldsExactHOL]

@[simp] theorem isWfCtxtExactHOL_nil :
    isWfCtxtExactHOL ([] : StructContextExact) = true := rfl

@[simp] theorem isWfCtxtExactHOL_cons (name : MlS) (info : StructInfoHOLExact)
    (rest : StructContextExact) :
    isWfCtxtExactHOL ((name, info) :: rest) =
      ((structContextLookupHOL name rest).isNone &&
        isWfFldsExactHOL rest info.fields && isWfCtxtExactHOL rest) := by
  simp only [isWfCtxtExactHOL]


/-- Extraction: a byte-ranged function declaration has a byte-ranged name. -/
theorem declByteRanged_function_name {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : DeclByteRanged (Flapjack.Decl.function fd)) :
    NameRanged fd.name :=
  h.1

/-- Extraction: a byte-ranged function declaration has a byte-ranged name. -/
theorem funDeclByteRanged_name {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : FunDeclByteRanged fd) :
    NameRanged fd.name :=
  h.1

end Flapjack.Pancake.PanLang
