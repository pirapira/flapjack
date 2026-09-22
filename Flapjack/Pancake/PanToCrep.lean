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

structure CompileContext (α : Type u) where
  vars : InfoMap (Shape × List Nat)
  functions : InfoMap (List (VarName × Shape) × Shape)
  exceptions : InfoMap α
  maxVar : Nat
  bytesInWord : α
  deriving Repr

@[hol "cakeml/pancake/pan_to_crepScript.sml" "cexp_heads_def"]
def cexpHeads : List (List (CrepExp α)) → Option (List (CrepExp α))
  | [] => some []
  | expressions :: rest =>
      match expressions, cexpHeads rest with
      | [], _ => none
      | _, none => none
      | expression :: _, some heads => some (expression :: heads)

/-- Cake's simplified `cexp_heads_simp` (`crepPropsScript.sml:11`): reject when
    some argument list is empty, otherwise keep every list's head.  The explicit
    `fallback` replaces Cake's total `HD`. -/
def cexpHeadsSimp (fallback : CrepExp α) :
    List (List (CrepExp α)) → Option (List (CrepExp α))
  | expressions =>
      if expressions.any (fun expression => expression.isEmpty) then none
      else some (expressions.map (fun expression => expression.headD fallback))

/-- Cake's `cexp_heads_eq` (`pan_to_crepProofScript.sml:104`): the case-shaped
    head collector agrees with the simplified one. -/
theorem cexpHeads_eq_cexpHeadsSimp (fallback : CrepExp α)
    (expressions : List (List (CrepExp α))) :
    cexpHeads expressions = cexpHeadsSimp fallback expressions := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      cases expression with
      | nil => simp [cexpHeads, cexpHeadsSimp]
      | cons head tail =>
          simp only [cexpHeads, ih, cexpHeadsSimp]
          split <;> simp_all

@[hol "cakeml/pancake/pan_to_crepScript.sml" "comp_field_def"]
def compileField [OfNat α 0] (index : Nat) :
    List Shape → List (CrepExp α) → List (CrepExp α) × Shape
  | [], _ => ([.const 0], .one)
  | shape :: shapes, expressions =>
      if index = 0 then (expressions.take (Shape.shapeSize shape), shape)
      else compileField (index - 1) shapes (expressions.drop (Shape.shapeSize shape))

@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_panop_def"]
def compilePanOp : PanOp → CrepOp
  | .mul => .mul

/-! Faithful port of `pan_to_crep$exp_hdl` from
    `cakeml/pancake/pan_to_crepScript.sml:106-112`.

    A variable absent from the finite map produces no code; a present variable
    is initialized from the global return area, one word per flattened local,
    with the assignments nested in source order.  The second component of the
    stored pair is the flattened word list; the shape is not consulted. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"]
def expHdlFiniteMap [OfNat α 0] [OfNat α 1] [Add α]
    (fm : FiniteMap VarName (Shape × List Nat)) (v : VarName) : CrepProg α :=
  match FLOOKUP fm v with
  | none => .skip
  | some (_, names) =>
      crepNestedSeq
        (panMap2 (fun destination source => .assign destination source)
          names (loadGlobals (0 : α) names.length))

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

/-- Executable handler-setup adapter.  It builds HOL's finite map from the
    association-list compiler context and invokes the tagged faithful port
    `expHdlFiniteMap`, so the executed call path uses the exact HOL definition.
    Untagged: HOL has no association-list helper.

    A known variable is initialized from the global return area, one word per
    flattened local, and the assignments are nested in source order. -/
def expHdl [BEq String] [OfNat α 0] [OfNat α 1] [Add α]
    (vars : InfoMap (Shape × List Nat)) (name : VarName) : CrepProg α :=
  expHdlFiniteMap (infoMapToFiniteMap vars) name

/-- The executable adapter computes the faithful finite-map definition on the
    bridged map. -/
theorem expHdl_eq_expHdlFiniteMap_bridge [BEq String] [OfNat α 0] [OfNat α 1] [Add α]
    (vars : InfoMap (Shape × List Nat)) (name : VarName) :
    expHdl vars name = expHdlFiniteMap (infoMapToFiniteMap vars) name := rfl

/-! Faithful port of `pan_to_crep$ret_var` from
    `cakeml/pancake/pan_to_crepScript.sml:114-119`.

    A return variable exists only for a one-word shape.  Pancake's `oHD`
    operation supplies the first flattened destination when one is present. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "ret_var_def"]
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

/-! Faithful port of `pan_to_crep$ret_hdl` from
    `cakeml/pancake/pan_to_crepScript.sml:122-127`.

    Only a multi-word `Comb` needs a handler that copies the returned global
    words into its flattened local destinations. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "ret_hdl_def"]
def retHdl [OfNat α 0] [OfNat α 1] [Add α]
    (shape : Shape) (names : List Nat) : CrepProg α :=
  match shape with
  | .one => .skip
  | .comb fields =>
      if 1 < Shape.shapeSize (.comb fields) then assignRet names
      else .skip
  | .named _ => .skip

/-! Faithful port of `pan_to_crep$wrap_rt` from
    `cakeml/pancake/pan_to_crepScript.sml:131-136`.

    The empty one-word return slot is normalized to no return slot; every
    other option is preserved unchanged. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "wrap_rt_def"]
def wrapRt : Option (Shape × List Nat) → Option (Shape × List Nat)
  | none => none
  | some (.one, []) => none
  | value => value

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

end Flapjack
