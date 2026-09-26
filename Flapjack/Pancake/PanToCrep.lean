import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.PanStatic
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.CrepLang.Prog

/-!
Executable expression lowering from Flapjack to Crepe.

This is the expression part of CakeML's `pan_to_crep` pass. Invalid or
ill-shaped inputs follow CakeML's extraction-friendly fallback behavior and
produce a zero constant.
-/

namespace Flapjack

universe v w

structure CompileContext (α : Type u) where
  vars : InfoMap (Shape × List Nat)
  functions : InfoMap (List (VarName × Shape) × Shape)
  exceptions : InfoMap α
  maxVar : Nat
  bytesInWord : α
  deriving Repr

/-! This is a Flapjack-specific context over the production `String` and
    `Shape` carriers. It is not HOL's `context` datatype: HOL uses MlString
    keys, `ShapeHOL` values, a word-indexed exception map, and finite-support
    maps. The exact record carrier is in `PanToCrep/ContextExact.lean` under
    bead `flapjack-4ac.2.1.1`; this production structure remains untagged. -/
structure PanToCrepHOLContext (α : Type) where
  vars : FiniteMap VarName (Shape × List Nat)
  funcs : FiniteMap FunName (List (VarName × Shape) × Shape)
  eids : FiniteMap ExceptionId α
  vmax : Nat

/-! FLAPJACK-SPECIFIC (not an exact HOL port). Source-reviewed decision
    (`flapjack-dlc.26`): the `@[hol "cakeml/pancake/pan_to_crepScript.sml"
    "mk_ctxt_def"]` tag stays withdrawn as a documented carrier mismatch.
    HOL `mk_ctxt_def` (`cakeml/pancake/pan_to_crepScript.sml:310-316`) stores
    `vars : varname |-> shape # num list`,
    `funcs : funname |-> ((varname # shape) list # shape)`,
    `eids : eid |-> 'a word`, `vmax : num`. There `varname`/`funname`/`eid`
    are `mlstring` (`panLangScript.sml:24-28`) and `shape` carries `stcname =
    mlstring` names (`panLangScript.sml:36-38`). This constructor instead takes
    production `VarName`/`FunName`/`ExceptionId` = `String` keys, the
    production `Shape` (whose `named` field is `String`) in the `vars`/`funcs`
    values, a generic `α` for the `eids` value rather than HOL's
    word-length-indexed `'a word`, and the extensional
    `FiniteMap α β := α → Option β` encoding of HOL's `fmap` (not the literal
    HOL carrier). The `names_as_string` qualifier cannot authorize the `Shape`
    value carrier or the changed `α`/`'a word` quantified eids type, and no
    `NameRanged` byte witness applies because this constructor produces a
    context, not a name. The exact MlString/`ShapeHOL`/`BitVec width` context
    carrier replacement is tracked by `flapjack-4ac.2.1.1`; the exact
    `compile_def` consumer is separately tracked by
    `flapjack-pxn.18.3.5.8.13`. -/
def panToCrepMkCtxtHOL (vars : FiniteMap VarName (Shape × List Nat))
    (funcs : FiniteMap FunName (List (VarName × Shape) × Shape))
    (vmax : Nat) (eids : FiniteMap ExceptionId α) : PanToCrepHOLContext α :=
  { vars, funcs, eids, vmax }

/-- HOL infers `cexp_heads_def` as `α list list -> α list option` because its
    body only inspects list structure; no `crepLang$exp` constructors constrain
    the element type. The production compiler uses this polymorphic definition
    at `β := CrepExp α`. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "cexp_heads_def"]
def cexpHeads {β : Type u} : List (List β) → Option (List β)
  | [] => some []
  | expressions :: rest =>
      match expressions, cexpHeads rest with
      | [], _ => none
      | _, none => none
      | expression :: _, some heads => some (expression :: heads)

/-- Exact HOL `comp_field_def` (`cakeml/pancake/pan_to_crepScript.sml:28-32`)
    over the MlString-backed `ShapeHOL` carrier and the positive-width
    `CrepExpHOL`.

    HOL returns `([Const 0w], One)` on an empty shape list, takes
    `size_of_shape sh` expressions for index `0`, and otherwise skips
    `size_of_shape sh` expressions and decrements the index. The Lean word
    width is the HOL word index (`BitVec width` with `[NeZero width]`), the
    zero literal is `CrepExpHOL.const 0`, and `sizeOfShapeHOL` is the already
    tagged `size_of_shape_def` over `ShapeHOL`. All constructor arities and
    field types match. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "comp_field_def"]
def compFieldHOL {width : Nat} [NeZero width] (index : Nat) :
    List Flapjack.Pancake.PanLang.ShapeHOL →
      List (CrepExpHOL width) →
        List (CrepExpHOL width) × Flapjack.Pancake.PanLang.ShapeHOL
  | [], _ => ([.const (0 : BitVec width)], .one)
  | shape :: shapes, expressions =>
      if index = 0 then
        (expressions.take (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape), shape)
      else
        compFieldHOL (index - 1) shapes
          (expressions.drop (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape))

/-- Flapjack-specific analogue of HOL `comp_field_def`. This implementation
    uses production `Shape`, whose named fields are Lean `String`, and a
    generic word carrier `α`; HOL `shape` names are `mlstring` and the result
    `crepLang$exp` is indexed by a positive word width. It is therefore not an
    exact HOL declaration and intentionally has no tag. The exact carrier port
    `compFieldHOL` over `ShapeHOL`/`CrepExpHOL` is tagged above, and
    `compileField_map_codecs` is the kernel bridge from this executed helper. -/
def compileField [OfNat α 0] (index : Nat) :
    List Shape → List (CrepExp α) → List (CrepExp α) × Shape
  | [], _ => ([.const 0], .one)
  | shape :: shapes, expressions =>
      if index = 0 then (expressions.take (Shape.shapeSize shape), shape)
      else compileField (index - 1) shapes (expressions.drop (Shape.shapeSize shape))

@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_panop_def"]
def compilePanOp : PanOp → CrepOp
  | .mul => .mul

/-! Clauses mirror `pan_to_crep$exp_hdl`
    (`cakeml/pancake/pan_to_crepScript.sml:106-112`).

    A variable absent from the finite map produces no code; a present variable
    is initialized from the global return area, one word per flattened local,
    with the assignments nested in source order.  The second component of the
    stored pair is the flattened word list; the shape is not consulted.

    Calls the generic `crepNestedSeq`; the width-indexed `crepNestedSeqW` is a
    definitional delegation of it, so this executed use computes the identical
    function (`flapjack-pxn.18.4.3.82`). Neither production helper is tagged.

    FLAPJACK-SPECIFIC (not an exact HOL port): HOL `exp_hdl` keys its finite map
    by `varname`, which is `mlstring`, while this carriage uses
    `VarName = String`.  The exact MlString-keyed syntax is tracked in
    `flapjack-pxn.18.3.5.8` / parent `flapjack-pxn.18.3.5.7.2`. -/
def expHdlFiniteMap {α : Type u}
    (fm : FiniteMap VarName (Shape × List Nat)) (v : VarName) : CrepProg α :=
  match FLOOKUP fm v with
  | none => .skip
  | some (_, names) =>
      crepNestedSeq
        (panMap2 (fun destination source => .assign destination source)
          names (loadGlobals (0 : BitVec 5) names.length))

/-! Flapjack-only representation bridge from the compiler's association-list
    `InfoMap` to the HOL finite map.  The compiler stores bindings
    most-recent-first; reversing and replaying them through `FUPDATE_LIST`
    (Cake's `FEMPTY |++ ...`) reproduces the finite map that Cake's `make_vmap`
    and `ctxt.vars |+ ...` updates build, so the later of two duplicate names
    wins the lookup, exactly as `FLOOKUP` does. -/
def infoMapToFiniteMap [BEq String] (entries : InfoMap β) : FiniteMap String β :=
  FUPDATE_LIST FEMPTY entries.reverse

theorem FUPDATE_LIST_append [BEq α] (fm : FiniteMap α β)
    (entries rest : List (α × β)) :
    FUPDATE_LIST fm (entries ++ rest) = FUPDATE_LIST (FUPDATE_LIST fm entries) rest := by
  simp [FUPDATE_LIST, List.foldl_append]

/-- Kernel-checked representation theorem: the list-backed first-match
    `lookupInfo` and `FLOOKUP` of the bridged finite map agree at every key,
    including duplicate names. This licenses the executable handler
    compilation to call `expHdlFiniteMap`; both use production String keys. -/
theorem lookupInfo_eq_flookup_infoMapToFiniteMap [BEq String] [LawfulBEq String]
    (name : String) (entries : InfoMap β) :
    lookupInfo name entries = FLOOKUP (infoMapToFiniteMap entries) name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [lookupInfo, infoMapToFiniteMap, List.reverse_cons, FUPDATE_LIST_append,
        FUPDATE_LIST_cons, FUPDATE_LIST_nil, FLOOKUP_update]
      by_cases h : (entry.1 == name) = true
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact ih

@[simp] theorem FLOOKUP_infoMapToFiniteMap [BEq String] [LawfulBEq String]
    (name : String) (entries : InfoMap β) :
    FLOOKUP (infoMapToFiniteMap entries) name = lookupInfo name entries :=
  (lookupInfo_eq_flookup_infoMapToFiniteMap name entries).symm

/-- Kernel-checked association-list adapter retained for tests and lemmas.  It
    builds a finite map from the compiler's `InfoMap` context and invokes
    `expHdlFiniteMap`. Production handler compilation does not use this
    wrapper: `compileProg` calls `expHdlFiniteMap` directly on
    `infoMapToFiniteMap context.vars`. Both definitions are untagged because
    their production keys/shapes use `String`, whereas HOL uses `mlstring`.
    HOL has no association-list helper.

    A known variable is initialized from the global return area, one word per
    flattened local, and the assignments are nested in source order. -/
def expHdl {α : Type u} [BEq String]
    (vars : InfoMap (Shape × List Nat)) (name : VarName) : CrepProg α :=
  expHdlFiniteMap (α := α) (infoMapToFiniteMap vars) name

/-- The executable adapter computes the faithful finite-map definition on the
    bridged map. -/
theorem expHdl_eq_expHdlFiniteMap_bridge {α : Type u} [BEq String]
    (vars : InfoMap (Shape × List Nat)) (name : VarName) :
    expHdl (α := α) vars name = expHdlFiniteMap (α := α) (infoMapToFiniteMap vars) name := rfl

/-! `pan_to_crep$exp_hdl` over the `MlString`-keyed / `ShapeHOL` / `CrepProgHOL`
    (`cakeml/pancake/pan_to_crepScript.sml:106-112`).

    HOL's equations are
    `exp_hdl fm v = case FLOOKUP fm v of
      | NONE => Skip
      | SOME (vshp, ns) => nested_seq (MAP2 Assign ns (load_globals 0w (LENGTH ns)))`.
    The `@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"]` tag is
    WITHDRAWN (bead `flapjack-2s5`). HOL quantifies over a finite map
    `varname |-> (shape # num list)`; this declaration instead takes
    `FiniteMap MlS (ShapeHOL × List Nat)`, the production raw function
    `MlString → Option (ShapeHOL × List Nat)`, which admits infinite support.
    Its quantified domain is therefore strictly broader than HOL's.

    The `fmap_as_finite_support` qualifier covers fields of a same-module
    carrier structure, not a bare map parameter. A faithful finite-map port
    is tracked by `flapjack-pxn.18.3.5.8.13.2`. This raw-map helper remains
    untagged infrastructure. The executed production `expHdlFiniteMap` is
    also untagged (its key is `VarName = String`); the checked bridge
    `crepProgToHOL_expHdlFiniteMap` relates the two under byte-ranged codecs. -/
def expHdlHOL {width : Nat} [NeZero width]
    (fm : FiniteMap Flapjack.Pancake.PanLang.MlS
      (Flapjack.Pancake.PanLang.ShapeHOL × List Nat))
    (v : Flapjack.Pancake.PanLang.MlS) : CrepProgHOL width :=
  match FLOOKUP fm v with
  | none => .skip
  | some (_, names) =>
      crepNestedSeqHOL
        (panMap2 (fun destination source => .assign destination source)
          names (loadGlobalsHOL (0 : BitVec 5) names.length))

/-- Codec from the production `String`-keyed finite map to the exact
    `MlString`-keyed HOL finite map. Names are encoded by the total
    `MlString.ofString`, and each stored shape by `shapeToHOL`; the flattened
    word lists are unchanged. Flapjack-only representation bridge. -/
def finiteMapToHOL (fm : FiniteMap String (Shape × List Nat)) :
    FiniteMap Flapjack.Pancake.PanLang.MlS
      (Flapjack.Pancake.PanLang.ShapeHOL × List Nat) :=
  fun key =>
    (fm (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map
      (fun pair => (Flapjack.Pancake.PanLang.shapeToHOL pair.1, pair.2))

/-- Cake's `MAP2` commutes with the program/expression codecs: mapping the
    production assignment list into the exact carriers equals assigning over the
    mapped value list. -/
theorem panMap2_assign_map {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExp (BitVec width))) :
    (panMap2
        (fun destination source =>
          (CrepProg.assign destination source : CrepProg (BitVec width)))
        names values).map crepProgToHOL
      = panMap2
          (fun destination source =>
            (CrepProgHOL.assign destination source : CrepProgHOL width))
          names (values.map crepExpToHOL) := by
  induction names generalizing values with
  | nil => simp [panMap2]
  | cons name names ih =>
      cases values with
      | nil => simp [panMap2]
      | cons value values => simp [panMap2, crepProgToHOL, ih]

/-- Narrow kernel bridge: on every byte-ranged variable name, encoding the
    production finite map and running the exact `expHdlHOL` agrees with the
    `crepProgToHOL` image of the executed `expHdlFiniteMap`. The production
    helper remains the executed one; routing the executed handler setup through
    the exact carrier is tracked by `flapjack-pxn.18.3.5.8.13`. -/
theorem crepProgToHOL_expHdlFiniteMap {width : Nat} [NeZero width]
    (fm : FiniteMap String (Shape × List Nat)) (v : String)
    (hv : ∀ c ∈ v.toList, c.toNat < 256) :
    crepProgToHOL (expHdlFiniteMap (α := BitVec width) fm v)
      = expHdlHOL (finiteMapToHOL fm)
          (Flapjack.Basis.Pure.MlString.ofString v) := by
  unfold expHdlFiniteMap expHdlHOL finiteMapToHOL
  simp only [FLOOKUP]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes v hv]
  cases h : fm v with
  | none => simp [crepProgToHOL]
  | some pair =>
      obtain ⟨shape, names⟩ := pair
      simp only [Option.map_some]
      rw [crepProgToHOL_crepNestedSeqHOL, panMap2_assign_map,
        crepExpMapToHOL_loadGlobals]

/-! Flapjack-specific analogue of `pan_to_crep$ret_var`
    (`cakeml/pancake/pan_to_crepScript.sml:114-119`).

    Clause-by-clause the HOL definition is
    `ret_var One ns = oHD ns`,
    `ret_var (Comb sh) ns = if size_of_shape (Comb sh) = 1 then oHD ns else NONE`,
    `ret_var (Named sh) ns = NONE` (comment "should never happen").
    `oHD` (`HOL/src/list/src/listScript.sml:5474`, `oHD l = case l of [] => NONE
    | h::_ => SOME h`) is exactly `List.head?`; `Shape.shapeSize` matches
    `size_of_shape` (`panLangScript.sml:174`) on `one`/`comb`/`named`.

    The production `Shape.Named` payload is a Lean `String` (`StructName`),
    whereas HOL uses `mlstring`. This function discards that payload. The
    current `names_as_string` policy classifies observed equality/map-key uses
    and byte-observable uses, not a discarded nested carrier; therefore this
    analogue remains untagged. The exact carrier port `retVarHOL` over
    `ShapeHOL` below is tagged, and `retVarHOL_shapeToHOL` is the kernel bridge.
    Direct HOL/Lean cases are retained in `ret_var_probe.out` and
    `RetVarParity.lean`. -/
def retVar (shape : Shape) (names : List Nat) : Option Nat :=
  match shape with
  | .one => names.head?
  | .comb fields =>
      if Shape.shapeSize (.comb fields) = 1 then names.head? else none
  | .named _ => none

/-! Exact port of HOL `pan_to_crep$ret_var`
    (`cakeml/pancake/pan_to_crepScript.sml:114-119`) over the faithful
    MlString-backed `ShapeHOL` carrier and the tagged `sizeOfShapeHOL`
    (`panLangScript.sml:174`).

    The HOL equations are
    `ret_var One ns = oHD ns`,
    `ret_var (Comb sh) ns = if size_of_shape (Comb sh) = 1 then oHD ns else NONE`,
    and `ret_var (Named sh) ns = NONE`, where `oHD`
    (`HOL/src/list/src/listScript.sml:5474`) is exactly `List.head?`.  The
    `named` case discards its `mlstring` payload, and all constructor arities
    and field types match `ShapeHOL`, so this is the exact statement.  The
    production `retVar` above mirrors these equations over `Flapjack.Shape`
    (String names) and stays untagged; `retVarHOL_shapeToHOL` below is the
    narrow kernel bridge on every production shape; the name is discarded, so
    no byte-rangedness premise is needed. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "ret_var_def"]
def retVarHOL (shape : Flapjack.Pancake.PanLang.ShapeHOL) (names : List Nat) : Option Nat :=
  match shape with
  | .one => names.head?
  | .comb shapes =>
      if Flapjack.Pancake.PanLang.sizeOfShapeHOL (.comb shapes) = 1 then names.head? else none
  | .named _ => none

private theorem foldl_shapeSize_add (a : Nat) (fields : List Shape) :
    List.foldl (fun total field => total + Shape.shapeSize field) a fields =
      a + List.foldl (fun total field => total + Shape.shapeSize field) 0 fields := by
  induction fields generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (a + Shape.shapeSize x), ih (0 + Shape.shapeSize x)]
      omega

mutual
  /-- `sizeOfShapeHOL` and `Shape.shapeSize` agree under the shape codec
      `shapeToHOL` (names are inert in both). -/
  theorem sizeOfShapeHOL_shapeToHOL : (s : Shape) →
      Flapjack.Pancake.PanLang.sizeOfShapeHOL (Flapjack.Pancake.PanLang.shapeToHOL s) =
        Shape.shapeSize s
    | .one => by simp [Flapjack.Pancake.PanLang.shapeToHOL]
    | .comb fields => by
      simp only [Flapjack.Pancake.PanLang.shapeToHOL,
        Flapjack.Pancake.PanLang.sizeOfShapeHOL, Shape.shapeSize]
      rw [sizeOfShapesHOL_shapeToHOL fields]
    | .named name => by simp [Flapjack.Pancake.PanLang.shapeToHOL]
  theorem sizeOfShapesHOL_shapeToHOL : (fields : List Shape) →
      Flapjack.Pancake.PanLang.sizeOfShapesHOL
          (fields.map Flapjack.Pancake.PanLang.shapeToHOL) =
        List.foldl (fun total field => total + Shape.shapeSize field) 0 fields
    | [] => rfl
    | field :: fields => by
      simp only [List.map_cons, List.foldl_cons, Nat.zero_add,
        Flapjack.Pancake.PanLang.sizeOfShapesHOL]
      rw [sizeOfShapeHOL_shapeToHOL field, sizeOfShapesHOL_shapeToHOL fields,
        foldl_shapeSize_add (Shape.shapeSize field) fields]
end

/-- Narrow kernel bridge: on every shape the exact `retVarHOL` agrees with the
    production `retVar` after the `shapeToHOL` codec.  Names are discarded by
    both, so no byte-rangedness hypothesis is needed. -/
theorem retVarHOL_shapeToHOL (shape : Shape) (names : List Nat) :
    retVarHOL (Flapjack.Pancake.PanLang.shapeToHOL shape) names = retVar shape names := by
  cases shape with
  | one => simp [retVarHOL, retVar, Flapjack.Pancake.PanLang.shapeToHOL]
  | comb fields =>
    simp only [retVarHOL, retVar, Flapjack.Pancake.PanLang.shapeToHOL,
      Flapjack.Pancake.PanLang.sizeOfShapeHOL, Shape.shapeSize]
    simp only [sizeOfShapesHOL_shapeToHOL fields]
  | named name => simp [retVarHOL, retVar, Flapjack.Pancake.PanLang.shapeToHOL]

/-- Narrow kernel bridge: mapping the production `compileField` result into
    the exact carriers agrees with `compFieldHOL`. The production helper is
    still the executed one; routing the executed expression lowering through
    the exact carrier is tracked by `flapjack-pxn.18.3.5.8.12`. -/
theorem compileField_map_codecs {width : Nat} [NeZero width] (index : Nat)
    (shapes : List Shape) (expressions : List (CrepExp (BitVec width))) :
    (compileField (α := BitVec width) index shapes expressions).1.map crepExpToHOL
        = (compFieldHOL index (shapes.map Flapjack.Pancake.PanLang.shapeToHOL)
            (expressions.map crepExpToHOL)).1
    ∧ Flapjack.Pancake.PanLang.shapeToHOL
        (compileField (α := BitVec width) index shapes expressions).2
        = (compFieldHOL index (shapes.map Flapjack.Pancake.PanLang.shapeToHOL)
            (expressions.map crepExpToHOL)).2 := by
  induction shapes generalizing index expressions with
  | nil =>
      rw [compileField.eq_1]
      simp only [List.map_nil]
      rw [compFieldHOL.eq_1]
      simp [crepExpToHOL.eq_1, Flapjack.Pancake.PanLang.shapeToHOL]
  | cons shape shapes ih =>
      by_cases h : index = 0
      · rw [compileField.eq_2]
        simp only [List.map_cons]
        rw [compFieldHOL.eq_2]
        simp only [if_pos h]
        constructor
        · rw [sizeOfShapeHOL_shapeToHOL, ← List.map_take]
        · trivial
      · rw [compileField.eq_2]
        simp only [List.map_cons]
        rw [compFieldHOL.eq_2]
        simp only [if_neg h]
        rw [sizeOfShapeHOL_shapeToHOL]
        rw [← List.map_drop]
        exact ih (index - 1) (expressions.drop (Shape.shapeSize shape))

/-- Kernel bridge: the executed `withShape` splits the value list exactly like
    the reviewed exact `withShapeHOL` after encoding every shape through the
    `shapeToHOL` codec.  The executed `withShape` measures blocks with the
    production `Shape.shapeSize`, while `withShapeHOL` uses `sizeOfShapeHOL`;
    `sizeOfShapeHOL_shapeToHOL` identifies the two on every shape (names are
    inert in both), so no byte-rangedness hypothesis is needed.  This is a
    Flapjack-specific production bridge (the HOL `panLang$with_shape` port is
    the tagged `withShapeHOL`), so it carries no `@[hol]` tag. -/
theorem withShape_codec {α : Type} (shapes : List Shape) (values : List α) :
    withShape shapes values =
      Flapjack.Pancake.PanLang.withShapeHOL
        (shapes.map Flapjack.Pancake.PanLang.shapeToHOL) values := by
  induction shapes generalizing values with
  | nil => simp [withShape, Flapjack.Pancake.PanLang.withShapeHOL]
  | cons shape shapes ih =>
      simp only [List.map_cons, withShape, Flapjack.Pancake.PanLang.withShapeHOL]
      rw [sizeOfShapeHOL_shapeToHOL shape, ih]


/-! Flapjack-only helper modeled on the commented-out `shape_vars_def` text
    (`cakeml/pancake/pan_to_crepScript.sml:319-324`); HOL does not define this
    function. The helper consumes the
    flattened word list one shape at a time: each result keeps exactly
    `size_of_shape sh` words, and the recursive call receives the remaining
    `DROP` suffix.  In particular, short input is not padded and excess input
    is not attached to the final shape. -/
def shapeVars (shapes : List Shape) (values : List α) : List (Shape × List α) :=
  match shapes with
  | [] => []
  | shape :: rest =>
      (shape, values.take (Shape.shapeSize shape)) ::
        shapeVars rest (values.drop (Shape.shapeSize shape))

/-! Flapjack-specific analogue of `pan_to_crep$ret_hdl`
    (`cakeml/pancake/pan_to_crepScript.sml:122-127`).

    Only a multi-word `Comb` needs a handler that copies the returned global
    words into its flattened local destinations. It uses production `Shape`
    with String-backed named fields and generic `CrepProg α`; HOL uses
    `mlstring`-named shapes and a word-width-indexed program. It stays untagged
    until those carriers are aligned; the exact `mlstring`-backed port is
    `retHdlHOL` below (tagged `ret_hdl_def`), related by the kernel bridge
    `crepProgToHOL_retHdl`. -/
def retHdl [OfNat α 0] [OfNat α 1] [Add α]
    (shape : Shape) (names : List Nat) : CrepProg α :=
  match shape with
  | .one => .skip
  | .comb fields =>
      if 1 < Shape.shapeSize (.comb fields) then assignRet names
      else .skip
  | .named _ => .skip

/-- Exact-shaped `assign_ret` helper over `CrepProgHOL`, mirroring HOL
    `crepLang$assign_ret_def` (`crepLangScript.sml:122-125`). The tagged
    `assign_ret_def` port is `assignRetW` over the production carrier; this
    helper exists so `retHdlHOL` can state `ret_hdl_def` exactly. -/
def assignRetHOL {width : Nat} [NeZero width] (names : List Nat) :
    CrepProgHOL width :=
  crepNestedSeqHOL
    (names.zipWith (fun name value => .assign name value)
      (loadGlobalsHOL (0 : BitVec 5) names.length))

/-- `crepProgToHOL` sends the production `assignRet` to the exact `assignRetHOL`. -/
theorem crepProgToHOL_assignRet {width : Nat} [NeZero width] (names : List Nat) :
    crepProgToHOL (assignRet (α := BitVec width) names) = assignRetHOL names := by
  have aux : ∀ (names : List Nat) (address : BitVec 5),
      crepProgToHOL
          (crepNestedSeq
            (names.zipWith (fun name value => CrepProg.assign name value)
              (loadGlobals (α := BitVec width) address names.length))) =
        crepNestedSeqHOL
          (names.zipWith (fun name value => CrepProgHOL.assign name value)
            (loadGlobalsHOL address names.length)) := by
    intro names
    induction names with
    | nil =>
        intro address
        simp [crepNestedSeq, crepNestedSeqHOL, loadGlobals, loadGlobalsHOL,
          crepProgToHOL]
    | cons name names ih =>
        intro address
        simp [crepNestedSeq, crepNestedSeqHOL, loadGlobals, loadGlobalsHOL,
          crepProgToHOL, crepExpToHOL, ih]
  unfold assignRet assignRetHOL
  exact aux names 0

/-- Exact port of HOL `pan_to_crep$ret_hdl` (`pan_to_crepScript.sml:122-127`) over
    the `mlstring`-backed `ShapeHOL` and the width-indexed `CrepProgHOL`. The
    `One` and `Named` cases emit `Skip`; a multi-word `Comb` emits `assign_ret`,
    which is the exact-shaped `assignRetHOL`. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "ret_hdl_def"]
def retHdlHOL {width : Nat} [NeZero width]
    (shape : Flapjack.Pancake.PanLang.ShapeHOL) (names : List Nat) :
    CrepProgHOL width :=
  match shape with
  | .one => .skip
  | .comb fields =>
      if 1 < Flapjack.Pancake.PanLang.sizeOfShapeHOL (.comb fields) then
        assignRetHOL names
      else .skip
  | .named _ => .skip

/-- Narrow kernel bridge: on every shape the `crepProgToHOL` image of the
    production `retHdl` equals the exact `retHdlHOL` after the `shapeToHOL`
    codec. Names are discarded by both, so no byte-rangedness hypothesis is
    needed. -/
theorem crepProgToHOL_retHdl {width : Nat} [NeZero width]
    (shape : Shape) (names : List Nat) :
    crepProgToHOL (retHdl (α := BitVec width) shape names) =
      retHdlHOL (Flapjack.Pancake.PanLang.shapeToHOL shape) names := by
  cases shape with
  | one =>
      simp [retHdl, retHdlHOL, Flapjack.Pancake.PanLang.shapeToHOL, crepProgToHOL]
  | comb fields =>
      simp only [Flapjack.Pancake.PanLang.shapeToHOL, retHdl, retHdlHOL]
      rw [show Flapjack.Pancake.PanLang.sizeOfShapeHOL
            (Flapjack.Pancake.PanLang.ShapeHOL.comb
              (fields.map Flapjack.Pancake.PanLang.shapeToHOL)) =
            List.foldl (fun total field => total + Shape.shapeSize field) 0 fields by
          rw [Flapjack.Pancake.PanLang.sizeOfShapeHOL_comb,
            sizeOfShapesHOL_shapeToHOL fields]]
      simp only [Shape.shapeSize]
      split <;> simp [crepProgToHOL, crepProgToHOL_assignRet]
  | named name =>
      simp [retHdl, retHdlHOL, Flapjack.Pancake.PanLang.shapeToHOL, crepProgToHOL]

/-! Flapjack-specific analogue of `pan_to_crep$wrap_rt`
    (`cakeml/pancake/pan_to_crepScript.sml:131-136`).

    Clause-by-clause the HOL definition is
    `wrap_rt NONE = NONE`,
    `wrap_rt (SOME (One, [])) = NONE`,
    `wrap_rt m = m`.
    The Lean equations match exactly: the empty one-word return slot is
    normalized to no return slot, and every other option is preserved
    unchanged.

    This declaration is untagged.  The production `Shape` `Named` constructor
    carries a Lean `String` (`StructName`) where HOL carries `mlstring`.
    `wrap_rt` never compares or byte-observes that name (it only tests the
    `One`/empty-list shape and otherwise returns its argument unchanged), so
    the difference is not byte-observable, but it is also not an
    equality/map-key use, and no truthful `names_as_string` classification
    exists yet.  A faithful tag needs an explicit unused/discarded
    nested-carrier classification in the qualifier policy (or an exact
    MlString-backed `ShapeHOL`); tracked as follow-up with `retVar`.

    Direct HOL rows (`none`/`empty_one`/`one_word`/`comb_empty`/`named`) are in
    `scripts/hol-probes/wrap_rt_probe.out`; Lean parity guards are in
    `Flapjack/Test/WrapRtParity.lean`.

    The exact `mlstring`-backed port is `wrapRtHOL` in this file (tagged
    `wrap_rt_def`), and `wrapRtHOL_map_shapeToHOL` relates the two through the
    `shapeToHOL` codec. -/
def wrapRt : Option (Shape × List Nat) → Option (Shape × List Nat)
  | none => none
  | some (.one, []) => none
  | value => value

/-! Exact HOL-shaped port of `pan_to_crep$wrap_rt`
    (`cakeml/pancake/pan_to_crepScript.sml:131-136`) over the `mlstring`-backed
    `ShapeHOL` carrier, so no String/MlString substitution remains: `NONE`
    stays `NONE`, the empty one-word slot `SOME (One, [])` is normalized to
    `NONE`, and every other option is returned unchanged. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "wrap_rt_def"]
def wrapRtHOL : Option (Flapjack.Pancake.PanLang.ShapeHOL × List Nat) → Option (Flapjack.Pancake.PanLang.ShapeHOL × List Nat)
  | none => none
  | some (.one, []) => none
  | value => value

/-! Narrow bridge: encoding the production input shape and running the exact
    `wrapRtHOL` gives the encoding of the production `wrapRt` result. The codec
    preserves `One`/`Comb`/`Named`, so this direction needs no byte-rangedness
    hypothesis. -/
theorem wrapRtHOL_map_shapeToHOL (n : Option (Shape × List Nat)) :
    wrapRtHOL (n.map (fun pair => (Flapjack.Pancake.PanLang.shapeToHOL pair.1, pair.2))) =
      (wrapRt n).map (fun pair => (Flapjack.Pancake.PanLang.shapeToHOL pair.1, pair.2)) := by
  cases n with
  | none => rfl
  | some pair =>
      obtain ⟨shape, names⟩ := pair
      cases shape <;> cases names <;>
        simp [wrapRtHOL, wrapRt, Flapjack.Pancake.PanLang.shapeToHOL]

/-! ## Return-path bridge (Flapjack-only)

Audit of the original development (`cakeml/pancake/pan_to_crepScript.sml`): the
executable `compile` definition calls `exp_hdl` (`:238`, `:250`, `:260`) and
`wrap_rt` (`:241`); it never calls `ret_hdl` (`:122`) or `ret_var` (`:114`).
Those two definitions are used only inside the `Call_Ret` case of
`pc_compile_correct` (`proofs/pan_to_crepProofScript.sml`, e.g. `:2622`,
`:2727`) and by `pan_to_wordProofScript.sml:1083` when simplifying
`exps_of (compile ...)`.  The executable path therefore already routes its
handler setup and call destination through the production `expHdlFiniteMap` /
`wrapRt`; re-routing `compileProg` through `retHdl` / `retVar` would be a
behavior change with no HOL counterpart.

The lemmas below are Flapjack-only infrastructure (HOL proves no such
statements); they compare the production `retHdl`, `retVar`, and
`expHdlFiniteMap` helpers with `assignRet` so a future return-path proof can
switch between the proof-level handler form and the emitted assignment form.
These helpers use production `Shape`/`VarName` carriers and carry no `@[hol]`
attribute.
Bead `flapjack-pxn.18.2.4.1`. -/

/-- Cake's `MAP2` truncates like `List.zipWith`, so the finite-map return
    handler body and `assignRet` emit the same program. -/
theorem panMap2_eq_zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ)
    (xs : List α) (ys : List β) : panMap2 f xs ys = xs.zipWith f ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [panMap2, ih]

/-- Production known-variable form of `pan_to_crep$exp_hdl`: when `FLOOKUP`
    finds the name, the emitted handler setup equals `assignRet`, which copies
    the global return slots into the flattened local. The exact HOL tag belongs
    to the separate width-indexed `assignRetW`. -/
theorem expHdlFiniteMap_eq_assignRet
    {α : Type u} [OfNat α 0] [OfNat α 1] [Add α]
    {fm : FiniteMap VarName (Shape × List Nat)} {v : VarName}
    {shape : Shape} {names : List Nat} (h : FLOOKUP fm v = some (shape, names)) :
    expHdlFiniteMap (α := α) fm v = assignRet (α := α) names := by
  unfold expHdlFiniteMap assignRet
  simp only [h]
  congr 1
  exact panMap2_eq_zipWith (α := Nat) (β := CrepExp α)
    (γ := CrepProg α) _ _ _

/-- Executable-adapter form of the previous lemma: the association-list
    `expHdl` computes the production `assignRet` whenever `lookupInfo` finds
    the variable. -/
theorem expHdl_eq_assignRet_of_lookupInfo {α : Type u} [BEq String] [LawfulBEq String]
    [OfNat α 0] [OfNat α 1] [Add α]
    {vars : InfoMap (Shape × List Nat)} {name : VarName}
    {shape : Shape} {names : List Nat}
    (h : lookupInfo name vars = some (shape, names)) :
    expHdl (α := α) vars name = assignRet names := by
  rw [expHdl_eq_expHdlFiniteMap_bridge (α := α)]
  exact expHdlFiniteMap_eq_assignRet (α := α)
    (fm := infoMapToFiniteMap vars) (v := name) (by simpa using h)

/-- The production `retHdl` on a multi-word `Comb` is `assignRet`. -/
theorem retHdl_comb_eq_assignRet [OfNat α 0] [OfNat α 1] [Add α]
    (fields : List Shape) (names : List Nat)
    (h : 1 < Shape.shapeSize (.comb fields)) :
    retHdl (.comb fields) names = assignRet names := by
  simp [retHdl, h]

/-- `pan_to_crep$ret_hdl` emits nothing for the one-word shapes. -/
theorem retHdl_one_word_eq_skip [OfNat α 0] [OfNat α 1] [Add α]
    (fields : List Shape) (names : List Nat)
    (h : ¬ 1 < Shape.shapeSize (.comb fields)) :
    retHdl (.comb fields) names = .skip := by
  simp [retHdl, h]

theorem retHdl_one_eq_skip [OfNat α 0] [OfNat α 1] [Add α] (names : List Nat) :
    retHdl (.one : Shape) names = .skip := rfl

theorem retHdl_named_eq_skip [OfNat α 0] [OfNat α 1] [Add α]
    (structName : StructName) (names : List Nat) :
    retHdl (.named structName) names = .skip := rfl

/-- `pan_to_crep$ret_var` selects the first flattened destination of a one-word
    shape and reports no return variable otherwise. -/
theorem retVar_one (names : List Nat) : retVar (.one : Shape) names = names.head? := rfl

theorem retVar_comb_eq_head (fields : List Shape) (names : List Nat)
    (h : Shape.shapeSize (.comb fields) = 1) :
    retVar (.comb fields) names = names.head? := by
  simp [retVar, h]

theorem retVar_comb_eq_none (fields : List Shape) (names : List Nat)
    (h : Shape.shapeSize (.comb fields) ≠ 1) :
    retVar (.comb fields) names = none := by
  simp [retVar, h]

theorem retVar_named (structName : StructName) (names : List Nat) :
    retVar (.named structName) names = none := rfl

/-! FLAPJACK-SPECIFIC source-shaped mirror of HOL
`compile_exp_def` (`cakeml/pancake/pan_to_crepScript.sml:39-108`). Its
recursive clauses follow the HOL cases, but it is not an exact port and carries
no `@[hol]` tag. This definition uses production `Exp α` (generic `Const α`),
production `Shape`/`CrepExp α` (with String-backed names), and
`CompileContext.vars : InfoMap ...`; HOL uses word-indexed `ExpHOL width`,
`ShapeHOL`/`CrepExpHOL width` with `MlString` names, and finite-map `context`.
The generic `[BEq α] [OfNat α 0] [Add α]` carrier cannot stand for HOL's
positive-width word type. In addition, Lean reads `bytesInWord` from the
arbitrary context for `Load`/`BytesInWord`, while HOL uses the fixed
word-width-derived `bytes_in_word`; `PanToCrepHOLContext` is also not exact yet.
The faithful exact-carrier port and production-path replacement are tracked by
`flapjack-4ac.2.5.1`, dependent on the exact PanLang/MlString carriers in
`flapjack-pxn.18.3.5.8`. -/
def compileExp [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : Exp α → List (CrepExp α) × Shape
  | .const value => ([.const value], .one)
  | .var .local name =>
      match lookupInfo name context.vars with
      | some (shape, names) => (names.map .var, shape)
      | none => ([.const 0], .one)
  | .var .global _ => ([.const 0], .one)
  | .rStruct expressions =>
      let compiled := compileExpList context expressions
      (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
  | .rField index expression =>
      let compiled := compileExp context expression
      match compiled.2 with
      | .comb shapes => compileField index shapes compiled.1
      | _ => ([.const 0], .one)
  | .nStruct _ _ => ([.const 0], .one)
  | .nField _ _ => ([.const 0], .one)
  | .load shape expression =>
      match compileExp context expression with
      | (expression :: _, _) =>
          (loadShape 0 context.bytesInWord (Shape.shapeSize shape) expression, shape)
      | _ => ([.const 0], .one)
  | .load32 expression =>
      match compileExp context expression with
      | (expression :: _, .one) => ([.load32 expression], .one)
      | _ => ([.const 0], .one)
  | .loadByte expression =>
      match compileExp context expression with
      | (expression :: _, .one) => ([.loadByte expression], .one)
      | _ => ([.const 0], .one)
  | .op operator expressions =>
      match cexpHeads (compileExpList context expressions |>.map Prod.fst) with
      | some expressions => ([.op operator expressions], .one)
      | none => ([.const 0], .one)
  | .panOp operator expressions =>
      match cexpHeads (compileExpList context expressions |>.map Prod.fst) with
      | some expressions => ([.crepOp (compilePanOp operator) expressions], .one)
      | none => ([.const 0], .one)
  | .cmp operator left right =>
      match compileExp context left, compileExp context right with
      | (left :: _, _), (right :: _, _) => ([.cmp operator left right], .one)
      | _, _ => ([.const 0], .one)
  | .shift operator left right =>
      match compileExp context left, compileExp context right with
      | (left :: _, _), (right :: _, _) => ([.shift operator left right], .one)
      | _, _ => ([.const 0], .one)
  | .baseAddr => ([.baseAddr], .one)
  | .topAddr => ([.topAddr], .one)
  | .bytesInWord => ([.const context.bytesInWord], .one)

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  compileExpList (context : CompileContext α) (expressions : List (Exp α)) :
      List (List (CrepExp α) × Shape) :=
    match expressions with
    | [] => []
    | expression :: expressions =>
        compileExp context expression :: compileExpList context expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

theorem compileExp_const [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (value : α) :
    compileExp context (.const value) = ([.const value], .one) := by
  simp [compileExp]

theorem compileExp_local_var [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape) (names : List Nat)
    (lookup : lookupInfo name context.vars = some (shape, names)) :
    compileExp context (.var .local name) = (names.map .var, shape) := by
  simp [compileExp, lookup]

theorem compileExp_bytesInWord [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) :
    compileExp context .bytesInWord = ([.const context.bytesInWord], .one) := by
  simp [compileExp]

/-- Production `.load` lowering with a machine-byte-width compile context agrees
    with Cake's fixed-stride `load_shape` (`loadShapeBytes`).  The pipeline passes
    `context.bytesInWord`; `hbytes` is the checked invariant that this field is
    the fixed machine byte width — `riscvBytesInWord_eq` certifies the RV64 entry
    points, which supply `8`. -/
theorem compileExp_load_eq_loadShapeBytes [BEq α] [OfNat α 0] [Add α]
    [CrepBytesInWord α] (context : CompileContext α)
    (hbytes : context.bytesInWord = CrepBytesInWord.bytesInWord)
    (shape : Shape) (expression : Exp α) (head : CrepExp α)
    (rest : List (CrepExp α)) (shape' : Shape)
    (hcompile : compileExp context expression = (head :: rest, shape')) :
    (compileExp context (.load shape expression)).1 =
      loadShapeBytes 0 (Shape.shapeSize shape) head := by
  rw [compileExp]
  simp only [hcompile]
  rw [loadShape_eq_loadShapeBytes_of_stride_eq _ _ _ _ hbytes]

/-- The executable RV64 entry point supplies `riscv64BytesInWord` as the context's
    `bytesInWord` (`Flapjack.compileMain`), so the production `.load` lowering is
    exactly Cake's fixed-stride `load_shape`.  This discharges the `hbytes`
    invariant of `compileExp_load_eq_loadShapeBytes` at the value the executable
    path actually uses, rather than in a hand-built test context. -/
theorem compileExp_load_riscv64
    (context : CompileContext (BitVec 64))
    (hbytes : context.bytesInWord = riscv64BytesInWord)
    (shape : Shape) (expression : Exp (BitVec 64)) (head : CrepExp (BitVec 64))
    (rest : List (CrepExp (BitVec 64))) (shape' : Shape)
    (hcompile : compileExp context expression = (head :: rest, shape')) :
    (compileExp context (.load shape expression)).1 =
      loadShapeBytes 0 (Shape.shapeSize shape) head :=
  compileExp_load_eq_loadShapeBytes context (by rw [hbytes, riscv64BytesInWord_eq])
    shape expression head rest shape' hcompile

end Flapjack
