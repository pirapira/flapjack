/-!
The core Pancake syntax.

This is the initial Lean counterpart of CakeML's `panLang` theory. Identifiers
are represented by `String`, while expressions remain polymorphic in their
word-value type, matching the polymorphic HOL AST.
-/

namespace Pancake

abbrev StructName := String
abbrev FieldName := String
abbrev VarName := String
abbrev FunName := String
abbrev ExceptionId := String
abbrev DeclarationName := String

inductive Shape where
  | one
  | comb (fields : List Shape)
  | named (name : StructName)
  deriving Repr

namespace Shape

def shapeSize : Shape → Nat
  | .one => 1
  | .comb fields => fields.foldl (fun total field => total + shapeSize field) 0
  | .named _ => 1

@[simp] theorem shapeSize_one : shapeSize Shape.one = 1 := by simp [shapeSize]

@[simp] theorem shapeSize_named (name : StructName) : shapeSize (Shape.named name) = 1 := by
  simp [shapeSize]

end Shape

inductive BinOp where
  | add
  | sub
  | and
  | or
  | xor
  deriving DecidableEq, Repr

inductive PanOp where
  | mul
  deriving DecidableEq, Repr

inductive Cmp where
  | equal
  | lower
  | less
  | test
  | notEqual
  | notLower
  | notLess
  | notTest
  deriving DecidableEq, Repr

inductive Shift where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

inductive VarKind where
  | local
  | global
  deriving DecidableEq, Repr

inductive Exp (α : Type u) where
  | const (value : α)
  | var (kind : VarKind) (name : VarName)
  | rStruct (fields : List (Exp α))
  | rField (index : Nat) (value : Exp α)
  | nStruct (name : StructName) (fields : List (FieldName × Exp α))
  | nField (name : FieldName) (value : Exp α)
  | load (shape : Shape) (address : Exp α)
  | load32 (address : Exp α)
  | loadByte (address : Exp α)
  | op (operator : BinOp) (args : List (Exp α))
  | panOp (operator : PanOp) (args : List (Exp α))
  | cmp (operator : Cmp) (left right : Exp α)
  | shift (operator : Shift) (left right : Exp α)
  | baseAddr
  | topAddr
  | bytesInWord

inductive OpSize where
  | op8
  | opW
  | op32
  | op16
  deriving DecidableEq, Repr

inductive PrimOp where
  | addCarry
  deriving DecidableEq, Repr

inductive Prog (α : Type u) where
  | skip
  | dec (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
  | assign (kind : VarKind) (name : VarName) (value : Exp α)
  | primitive (name : VarName) (operator : PrimOp) (args : List (Exp α))
  | store (address value : Exp α)
  | store32 (address value : Exp α)
  | storeByte (address value : Exp α)
  | seq (first second : Prog α)
  | ite (condition : Exp α) (thenBranch elseBranch : Prog α)
  | while (condition : Exp α) (body : Prog α)
  | break
  | continue
  | call (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α))) (name : FunName) (args : List (Exp α))
  | decCall (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α)
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Exp α)
  | raise (exception : ExceptionId) (value : Exp α)
  | return (value : Exp α)
  | shMemLoad (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
  | shMemStore (size : OpSize) (address value : Exp α)
  | tick
  | annot (tag text : String)

structure FunDecl (α : Type u) where
  name : FunName
  inline : Bool
  exported : Bool
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape

inductive Decl (α : Type u) where
  | function (declaration : FunDecl α)
  | decl (shape : Shape) (name : DeclarationName) (value : Exp α)
  | exnDecl (exception : ExceptionId) (shape : Shape)
  | name (struct : StructName) (fields : List (FieldName × Shape))

def nestedSeq : List (Prog α) → Prog α
  | [] => .skip
  | statement :: statements => .seq statement (nestedSeq statements)

def expLocalVars : Exp α → List VarName
  | .const _ => []
  | .var .local name => [name]
  | .var .global _ => []
  | .rStruct fields => expLocalVarsList fields
  | .rField _ value => expLocalVars value
  | .nStruct _ fields => expLocalVarsFieldList fields
  | .nField _ value => expLocalVars value
  | .load _ address => expLocalVars address
  | .load32 address => expLocalVars address
  | .loadByte address => expLocalVars address
  | .op _ args => expLocalVarsList args
  | .panOp _ args => expLocalVarsList args
  | .cmp _ left right => expLocalVars left ++ expLocalVars right
  | .shift _ left right => expLocalVars left ++ expLocalVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  expLocalVarsList (expressions : List (Exp α)) : List VarName :=
    match expressions with
    | [] => []
    | expression :: expressions => expLocalVars expression ++ expLocalVarsList expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  expLocalVarsFieldList (fields : List (FieldName × Exp α)) : List VarName :=
    match fields with
    | [] => []
    | (_, expression) :: fields => expLocalVars expression ++ expLocalVarsFieldList fields
  termination_by sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def expGlobalVars : Exp α → List VarName
  | .const _ => []
  | .var .local _ => []
  | .var .global name => [name]
  | .rStruct fields => expGlobalVarsList fields
  | .rField _ value => expGlobalVars value
  | .nStruct _ fields => expGlobalVarsFieldList fields
  | .nField _ value => expGlobalVars value
  | .load _ address => expGlobalVars address
  | .load32 address => expGlobalVars address
  | .loadByte address => expGlobalVars address
  | .op _ args => expGlobalVarsList args
  | .panOp _ args => expGlobalVarsList args
  | .cmp _ left right => expGlobalVars left ++ expGlobalVars right
  | .shift _ left right => expGlobalVars left ++ expGlobalVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  expGlobalVarsList (expressions : List (Exp α)) : List VarName :=
    match expressions with
    | [] => []
    | expression :: expressions => expGlobalVars expression ++ expGlobalVarsList expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  expGlobalVarsFieldList (fields : List (FieldName × Exp α)) : List VarName :=
    match fields with
    | [] => []
    | (_, expression) :: fields => expGlobalVars expression ++ expGlobalVarsFieldList fields
  termination_by sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

end Pancake
