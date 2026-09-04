import Pancake.Language

/-!
Static-checker data and shape-context operations.

This module is the first executable part of the front end after the AST. It
ports the small, reusable pieces of CakeML's `panStatic` theory; full
expression/program checking is intentionally layered on top of these types.
-/

namespace Pancake

structure StructInfo where
  fields : List (FieldName × Shape)
  size : Nat
  deriving Repr

abbrev StructContext := List (StructName × StructInfo)
abbrev InfoMap (α : Type u) := List (String × α)

def lookupInfo [BEq String] (name : String) : InfoMap α → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if candidate == name then some value else lookupInfo name entries

def isWfShape (context : StructContext) : Shape → Bool
  | .one => true
  | .comb shapes => isWfShapeList context shapes
  | .named name => (lookupInfo name context).isSome

termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  isWfShapeList (context : StructContext) : List Shape → Bool
    | [] => true
    | shape :: shapes => isWfShape context shape && isWfShapeList context shapes
  termination_by shapes => sizeOf shapes
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def isWfFields (context : StructContext) : List (FieldName × Shape) → Bool
  | [] => true
  | (_, shape) :: fields => isWfShape context shape && isWfFields context fields

def isWfContext : StructContext → Bool
  | [] => true
  | (name, info) :: context =>
      (lookupInfo name context).isNone &&
        isWfFields context info.fields && isWfContext context

def shapeSizeWithContext (context : StructContext) : Shape → Nat
  | .one => 1
  | .comb shapes => shapes.foldl (fun total shape => total + shapeSizeWithContext context shape) 0
  | .named name => ((lookupInfo name context).map StructInfo.size).getD 1

inductive StatErr where
  | scope (message : String)
  | warning (message : String)
  | general (message : String)
  | shape (message : String)
  deriving DecidableEq, Repr

abbrev StaticResult (α : Type u) := Except StatErr α × List StatErr

inductive Based where
  | based
  | notBased
  | trusted
  | notTrusted
  deriving DecidableEq, Repr

inductive ShapedBased where
  | word (basedness : Based)
  | struct (fields : List ShapedBased)
  | named (name : StructName) (fields : List (FieldName × ShapedBased))
  deriving Repr

inductive Reachable where
  | isReach
  | notReach
  | warnReach
  deriving DecidableEq, Repr

inductive LastStmt where
  | retLast
  | raiseLast
  | tailLast
  | breakLast
  | contLast
  | condExitLast
  | invisLast
  | otherLast
  deriving DecidableEq, Repr

structure FuncInfo where
  returnShape : Shape
  params : List (VarName × Shape)
  deriving Repr

structure LocalInfo where
  shapedBased : ShapedBased
  deriving Repr

structure GlobalInfo where
  shape : Shape
  deriving Repr

inductive Scope where
  | funScope (function : FunName) (location : String)
  | declScope (name : VarName)
  | structScope (struct : StructName) (field : FieldName)
  | topLevel
  deriving Repr

structure Context where
  locals : InfoMap LocalInfo
  globals : InfoMap GlobalInfo
  functions : InfoMap FuncInfo
  exceptions : InfoMap Shape
  structs : StructContext
  scope : Scope
  inLoop : Bool
  reachable : Reachable
  last : LastStmt
  location : String
  deriving Repr

structure ExpReturn where
  shapedBased : ShapedBased
  deriving Repr

structure ExpsReturn where
  shapedBased : List ShapedBased
  deriving Repr

structure ProgReturn where
  exitsFunction : Bool
  exitsLoop : Bool
  last : LastStmt
  variableDelta : InfoMap LocalInfo
  currentLocation : String
  deriving Repr

inductive ScopedId where
  | variable
  | function
  | struct
  deriving DecidableEq, Repr

def validateDecl (context : StructContext) : Decl α → Bool
  | .function declaration =>
      declaration.params.all (fun (_, shape) => isWfShape context shape) &&
        isWfShape context declaration.returnShape
  | .decl shape _ _ => isWfShape context shape
  | .exnDecl _ shape => isWfShape context shape
  | .name name fields =>
      (lookupInfo name context).isNone && isWfFields context fields

end Pancake
