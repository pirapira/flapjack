import Pancake.Crepe
import Pancake.Static

/-!
Executable expression lowering from Pancake to Crepe.

This is the expression part of CakeML's `pan_to_crep` pass. Invalid or
ill-shaped inputs follow CakeML's extraction-friendly fallback behavior and
produce a zero constant.
-/

namespace Pancake

structure CompileContext (α : Type u) where
  vars : InfoMap (Shape × List Nat)
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

def compileField [OfNat α 0] (index : Nat) :
    List Shape → List (CrepExp α) → List (CrepExp α) × Shape
  | [], _ => ([.const 0], .one)
  | shape :: shapes, expressions =>
      if index = 0 then (expressions.take (Shape.shapeSize shape), shape)
      else compileField (index - 1) shapes (expressions.drop (Shape.shapeSize shape))

def compilePanOp : PanOp → CrepOp
  | .mul => .mul

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
  | .bytesInWord => ([.const 0], .one)

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

end Pancake
