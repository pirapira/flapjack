/-!
The core Flapjack syntax.

This is the initial Lean counterpart of CakeML's `panLang` theory. Identifiers
are represented by `String`, while expressions remain polymorphic in their
word-value type, matching the polymorphic HOL AST.
-/

namespace Flapjack

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

/-! Exact source counterpart of Pancake's `shape_to_str_def`. -/
def shapeToString : Shape → String
  | .one => "1"
  | .comb [] => "{}"
  | .comb (head :: tail) =>
      "{" ++ shapeToString head ++
        tail.foldl (fun result field => result ++ "," ++ shapeToString field) "" ++ "}"
  | .named name => name

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

/-!
Pancake has two order relations on words: `Lower` is unsigned while `Less`
is signed. Keeping them in a target-supplied interface avoids accidentally
using Lean's single `LT` relation for both source-language operations.
The fallback instance below is useful for abstract scalar models whose only
available order is `LT`; word targets should provide their own instance.
-/

class PanCmp (α : Type u) where
  lower : α → α → Bool
  less : α → α → Bool

instance (priority := 10) panCmpOfLt [LT α]
    [DecidableRel (fun left right : α => left < right)] : PanCmp α where
  lower left right := decide (left < right)
  less left right := decide (left < right)

inductive Shift where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

/-!
The source language distinguishes logical and arithmetic right shifts, and
also exposes rotate-right.  These operations are separate from Lean's
homogeneous `ShiftRight` class because the latter denotes logical shift for
the target words.
-/

class ArithmeticShiftRight (α : Type u) where
  arithmeticShiftRight : α → α → α

class RotateRightOp (α : Type u) where
  rotateRight : α → α → α

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
  deriving Repr

inductive OpSize where
  | op8
  | opW
  | op32
  | op16
  deriving DecidableEq, Repr

inductive PrimOp where
  | addCarry
  deriving DecidableEq, Repr

/-! The source `word_sh` operation receives a natural shift amount extracted
    from a target word.  Targets provide the word width and this extraction so
    the generic source evaluator can preserve CakeML's out-of-range failure
    rule. -/
class PanShiftWidth (α : Type u) where
  width : Nat
  amount : α → Nat

/-! Natural-number pipeline instantiations (used by pass-local fixtures) treat
    the word width as the 64-bit RISC-V target and extract shift amounts
    unchanged. -/
instance natPanShiftWidth : PanShiftWidth Nat where
  width := 64
  amount := id

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
  deriving Repr

structure FunDecl (α : Type u) where
  name : FunName
  inline : Bool
  exported : Bool
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape
  deriving Repr

inductive Decl (α : Type u) where
  | function (declaration : FunDecl α)
  | decl (shape : Shape) (name : DeclarationName) (value : Exp α)
  | exnDecl (exception : ExceptionId) (shape : Shape)
  | name (struct : StructName) (fields : List (FieldName × Shape))
  deriving Repr

/-! Direct source-shaped counterpart of `panLang$inlinable`: only function
    declarations expose their inline bit. -/
def inlinable : Decl α → Bool
  | .function declaration => declaration.inline
  | _ => false

def nestedSeq : List (Prog α) → Prog α
  | [] => .skip
  | statement :: statements => .seq statement (nestedSeq statements)

/-! The exception identifiers syntactically reachable from a Pancake program.
    This follows `panLang$exp_ids_def`; in particular, a call contributes its
    handler identifier and the identifiers reachable in that handler, while
    ordinary calls and all non-handler forms contribute no identifiers. -/
def expIds : Prog α → List ExceptionId
  | .skip => []
  | .dec _ _ _ body => expIds body
  | .assign _ _ _ => []
  | .primitive _ _ _ => []
  | .store _ _ => []
  | .store32 _ _ => []
  | .storeByte _ _ => []
  | .seq first second => expIds first ++ expIds second
  | .ite _ thenBranch elseBranch => expIds thenBranch ++ expIds elseBranch
  | .while _ body => expIds body
  | .break => []
  | .continue => []
  | .call (some (_, some (exception, _, handler))) _ _ =>
      exception :: expIds handler
  | .call _ _ _ => []
  | .decCall _ _ _ _ body => expIds body
  | .extCall _ _ _ _ _ => []
  | .raise exception _ => [exception]
  | .return _ => []
  | .shMemLoad _ _ _ _ => []
  | .shMemStore _ _ _ => []
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Direct source-shaped counterpart of `panLang$fun_ids`: collect the
    statically referenced function names, including call-handler bodies and
    declaration-call bodies. -/
def funIds : Prog α → List FunName
  | .dec _ _ _ body => funIds body
  | .seq first second => funIds first ++ funIds second
  | .ite _ thenBranch elseBranch => funIds thenBranch ++ funIds elseBranch
  | .while _ body => funIds body
  | .call (some (_, some (_, _, handler))) name _ => name :: funIds handler
  | .call _ name _ => [name]
  | .decCall _ _ function _ body => function :: funIds body
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Split a flat value list according to the source shape sizes.  This is the
    direct Lean counterpart of `panLang$with_shape`; values left over after
    the requested shapes are intentionally ignored, and short inputs are
    handled by `List.take`/`List.drop` just like CakeML's `TAKE`/`DROP`. -/
def withShape : List Shape → List α → List (List α)
  | [], _ => []
  | shape :: shapes, values =>
      values.take (Shape.shapeSize shape) ::
        withShape shapes (values.drop (Shape.shapeSize shape))
termination_by shapes => sizeOf shapes
decreasing_by
  all_goals decreasing_trivial

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

/-! Direct source-shaped counterpart of `panLang$free_var_ids`.  The
    expression helper is the existing `expLocalVars`, which mirrors the
    source `var_exp` distinction between local and global variables. -/
def freeVarIds : Prog α → List VarName
  | .dec name _ value body =>
      expLocalVars value ++ (freeVarIds body).filter (fun vname => vname != name)
  | .seq first second => freeVarIds first ++ freeVarIds second
  | .ite condition thenBranch elseBranch =>
      expLocalVars condition ++ freeVarIds thenBranch ++ freeVarIds elseBranch
  | .while condition body => expLocalVars condition ++ freeVarIds body
  | .assign kind name value =>
      (if kind == .local then [name] else []) ++ expLocalVars value
  | .primitive name _ arguments => name :: arguments.flatMap expLocalVars
  | .store address value => expLocalVars address ++ expLocalVars value
  | .store32 address value => expLocalVars address ++ expLocalVars value
  | .storeByte address value => expLocalVars address ++ expLocalVars value
  | .raise _ value => expLocalVars value
  | .return value => expLocalVars value
  | .extCall _ configuration configurationLength array arrayLength =>
      expLocalVars configuration ++ expLocalVars configurationLength ++
        expLocalVars array ++ expLocalVars arrayLength
  | .shMemLoad _ kind name address =>
      (if kind == .local then [name] else []) ++ expLocalVars address
  | .shMemStore _ address value => expLocalVars address ++ expLocalVars value
  | .call (some (none, some (_, exceptionName, handler))) _ arguments =>
      exceptionName :: freeVarIds handler ++ arguments.flatMap expLocalVars
  | .call (some (some (kind, name), some (_, exceptionName, handler))) _ arguments =>
      (if kind == .local then [name] else []) ++
        exceptionName :: freeVarIds handler ++ arguments.flatMap expLocalVars
  | .call (some (some (kind, name), none)) _ arguments =>
      (if kind == .local then [name] else []) ++ arguments.flatMap expLocalVars
  | .call (some (none, none)) _ arguments => arguments.flatMap expLocalVars
  | .call none _ arguments => arguments.flatMap expLocalVars
  | .decCall name _ _ arguments body =>
      name :: freeVarIds body ++ arguments.flatMap expLocalVars
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

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

end Flapjack
