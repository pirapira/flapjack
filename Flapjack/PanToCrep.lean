import Flapjack.HolRef
import Flapjack.Crepe
import Flapjack.Static

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

def compileField [OfNat α 0] (index : Nat) :
    List Shape → List (CrepExp α) → List (CrepExp α) × Shape
  | [], _ => ([.const 0], .one)
  | shape :: shapes, expressions =>
      if index = 0 then (expressions.take (Shape.shapeSize shape), shape)
      else compileField (index - 1) shapes (expressions.drop (Shape.shapeSize shape))

def compilePanOp : PanOp → CrepOp
  | .mul => .mul

/-! Faithful port of `pan_to_crep$exp_hdl` from
    `cakeml/pancake/pan_to_crepScript.sml:106-112`.

    A known variable is initialized from the global return area, one word per
    flattened local, and the assignments are nested in source order. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "exp_hdl_def"]
def expHdl [OfNat α 0] [OfNat α 1] [Add α]
    (vars : InfoMap (Shape × List Nat)) (name : VarName) : CrepProg α :=
  match lookupInfo name vars with
  | none => .skip
  | some (_, names) =>
      crepNestedSeq
        (List.zipWith (fun destination source => .assign destination source)
          names (loadGlobals 0 names.length))

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

/-! Source-shaped port of CakeML Pancake's `shape_vars_def`
    (`cakeml/pancake/pan_to_crepScript.sml:319-322`).  The source consumes the
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

end Flapjack
