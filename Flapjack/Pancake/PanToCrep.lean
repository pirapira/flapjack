import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.PanStatic

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

/-! HOL's `context` record in `pan_to_crepScript.sml` uses finite maps, not
    `InfoMap` lists. This context preserves that representation directly. -/
structure PanToCrepHOLContext (α : Type) where
  vars : FiniteMap VarName (Shape × List Nat)
  funcs : FiniteMap FunName (List (VarName × Shape) × Shape)
  eids : FiniteMap ExceptionId α
  vmax : Nat

/- FLAPJACK-SPECIFIC (not an exact HOL port): HOL `mk_ctxt_def` keys
   `vars`/`funcs`/`eids` by `varname`/`funname`/`eid`, which
   `panLangScript.sml`/`crepLangScript.sml` alias to `mlstring`, while this
   Lean carrier keys them by `VarName`/`FunName`/`ExceptionId` = `String`.
   The exact MlString-keyed syntax is tracked in `flapjack-pxn.18.3.5.8` /
   parent `flapjack-pxn.18.3.5.7.2`. -/
def panToCrepMkCtxtHOL (vars : FiniteMap VarName (Shape × List Nat))
    (funcs : FiniteMap FunName (List (VarName × Shape) × Shape))
    (vmax : Nat) (eids : FiniteMap ExceptionId α) : PanToCrepHOLContext α :=
  { vars, funcs, eids, vmax }

@[hol "cakeml/pancake/pan_to_crepScript.sml" "cexp_heads_def"]
def cexpHeads : List (List (CrepExp α)) → Option (List (CrepExp α))
  | [] => some []
  | expressions :: rest =>
      match expressions, cexpHeads rest with
      | [], _ => none
      | _, none => none
      | expression :: _, some heads => some (expression :: heads)

/-- Flapjack-specific analogue of HOL `comp_field_def`. This implementation
    uses production `Shape`, whose named fields are Lean `String`, and a
    generic word carrier `α`; HOL `shape` names are `mlstring` and the result
    `crepLang$exp` is indexed by a positive word width. It is therefore not an
    exact HOL declaration and intentionally has no tag until both carriers are
    represented exactly. -/
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

    Calls the generic `crepNestedSeq`; the tagged width-indexed `crepNestedSeqW`
    is a definitional delegation of it, so this executed use computes the
    identical function (`flapjack-pxn.18.4.3.82`).

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
    including duplicate names.  This is what licenses the executable handler
    compilation to call the faithful `expHdlFiniteMap`. -/
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
    builds HOL's finite map from the compiler's `InfoMap` context and invokes
    the tagged faithful port `expHdlFiniteMap`.  Production handler compilation
    does not use this wrapper: `compileProg` calls `expHdlFiniteMap` directly on
    `infoMapToFiniteMap context.vars`, so the executed path is the tagged
    definition itself.  Untagged: HOL has no association-list helper.

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

/-! Flapjack-specific analogue of `pan_to_crep$ret_var`
    (`cakeml/pancake/pan_to_crepScript.sml:114-119`).

    A return variable exists only for a one-word shape.  Pancake's `oHD`
    operation supplies the first flattened destination when one is present.
    This declaration consumes production `Shape`, whose `Named` field is a
    Lean `String`; HOL's shape uses an `mlstring` name. The equations mirror
    HOL, but the input carrier differs, so this declaration is untagged. -/
def retVar (shape : Shape) (names : List Nat) : Option Nat :=
  match shape with
  | .one => names.head?
  | .comb fields =>
      if Shape.shapeSize (.comb fields) = 1 then names.head? else none
  | .named _ => none

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
    `mlstring`-named shapes and a word-width-indexed program. It is untagged
    until those carriers are aligned. -/
def retHdl [OfNat α 0] [OfNat α 1] [Add α]
    (shape : Shape) (names : List Nat) : CrepProg α :=
  match shape with
  | .one => .skip
  | .comb fields =>
      if 1 < Shape.shapeSize (.comb fields) then assignRet names
      else .skip
  | .named _ => .skip

/-! Flapjack-specific analogue of `pan_to_crep$wrap_rt`
    (`cakeml/pancake/pan_to_crepScript.sml:131-136`).

    The empty one-word return slot is normalized to no return slot; every
    other option is preserved unchanged. The production `Shape` nested in the
    option uses String-backed named fields, while HOL uses `mlstring`; the
    equations match but the carriers do not, so this declaration is untagged. -/
def wrapRt : Option (Shape × List Nat) → Option (Shape × List Nat)
  | none => none
  | some (.one, []) => none
  | value => value

/-! ## Return-path bridge (Flapjack-only)

Audit of the original development (`cakeml/pancake/pan_to_crepScript.sml`): the
executable `compile` definition calls `exp_hdl` (`:238`, `:250`, `:260`) and
`wrap_rt` (`:241`); it never calls `ret_hdl` (`:122`) or `ret_var` (`:114`).
Those two definitions are used only inside the `Call_Ret` case of
`pc_compile_correct` (`proofs/pan_to_crepProofScript.sml`, e.g. `:2622`,
`:2727`) and by `pan_to_wordProofScript.sml:1083` when simplifying
`exps_of (compile ...)`.  The executable path therefore already routes its
handler setup and call destination through the faithful `expHdlFiniteMap` /
`wrapRt`; re-routing `compileProg` through `retHdl` / `retVar` would be a
behavior change with no HOL counterpart.

The lemmas below are Flapjack-only infrastructure (HOL proves no such
statements); they connect the tagged `ret_hdl_def`, `ret_var_def`, and
`exp_hdl_def` to the tagged `assign_ret_def` so a future return-path proof can
switch between the proof-level handler form and the emitted assignment form.
They carry no `@[hol]` attribute because HOL has no corresponding declaration.
Bead `flapjack-pxn.18.2.4.1`. -/

/-- Cake's `MAP2` truncates like `List.zipWith`, so the finite-map return
    handler body and `assignRet` emit the same program. -/
theorem panMap2_eq_zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ)
    (xs : List α) (ys : List β) : panMap2 f xs ys = xs.zipWith f ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [panMap2, ih]

/-- Known-variable form of `pan_to_crep$exp_hdl`: when `FLOOKUP` finds the
    name, the emitted handler setup is exactly the tagged `assign_ret`
    program that copies the global return slots into the flattened local. -/
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
    `expHdl` computes the tagged `assign_ret` whenever `lookupInfo` finds the
    variable. -/
theorem expHdl_eq_assignRet_of_lookupInfo {α : Type u} [BEq String] [LawfulBEq String]
    [OfNat α 0] [OfNat α 1] [Add α]
    {vars : InfoMap (Shape × List Nat)} {name : VarName}
    {shape : Shape} {names : List Nat}
    (h : lookupInfo name vars = some (shape, names)) :
    expHdl (α := α) vars name = assignRet names := by
  rw [expHdl_eq_expHdlFiniteMap_bridge (α := α)]
  exact expHdlFiniteMap_eq_assignRet (α := α)
    (fm := infoMapToFiniteMap vars) (v := name) (by simpa using h)

/-- `pan_to_crep$ret_hdl` on a multi-word `Comb` is the tagged `assign_ret`. -/
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
