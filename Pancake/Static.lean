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

def staticOk (value : α) : StaticResult α := (Except.ok value, [])

def staticError (error : StatErr) : StaticResult α := (Except.error error, [])

def staticBind (result : StaticResult α) (continuation : α → StaticResult β) :
    StaticResult β :=
  match result with
  | (Except.error error, warnings) => (Except.error error, warnings)
  | (Except.ok value, warnings) =>
      let next := continuation value
      (next.1, warnings ++ next.2)

def shapedBasedFromShape (context : StructContext) : Shape → Option ShapedBased
  | .one => some (.word .trusted)
  | .comb shapes =>
      match shapedBasedFromShapes context shapes with
      | some fields => some (.struct fields)
      | none => none
  | .named name =>
      match lookupInfo name context with
      | some _ => some (.named name [])
      | none => none
termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  shapedBasedFromShapes (context : StructContext) : List Shape → Option (List ShapedBased)
    | [] => some []
    | shape :: shapes => do
        let shaped ← shapedBasedFromShape context shape
        let rest ← shapedBasedFromShapes context shapes
        pure (shaped :: rest)
  termination_by shapes => sizeOf shapes
    decreasing_by
      all_goals first | sizeOf_list_dec | decreasing_trivial

def shapedBasedFieldAt : Nat → ShapedBased → Option ShapedBased
  | index, .struct fields => shapedBasedFieldAtList index fields
  | _, _ => none
where
  shapedBasedFieldAtList : Nat → List ShapedBased → Option ShapedBased
    | _, [] => none
    | 0, field :: _ => some field
    | index + 1, _ :: fields => shapedBasedFieldAtList index fields

def shapedBasedFieldNamed (name : FieldName) : ShapedBased → Option ShapedBased
  | .named _ fields => lookupInfo name fields
  | _ => none

def shapedBasedIsWord : ShapedBased → Bool
  | .word _ => true
  | _ => false

def shapedBasedSameShape : ShapedBased → ShapedBased → Bool
  | .word _, .word _ => true
  | .struct left, .struct right => shapedBasedSameShapes left right
  | .named left _, .named right _ => left == right
  | _, _ => false
where
  shapedBasedSameShapes : List ShapedBased → List ShapedBased → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        shapedBasedSameShape left right && shapedBasedSameShapes lefts rights
    | _, _ => false

def shapedBasedFieldsMatch (context : StructContext)
    : List (FieldName × Shape) → List (FieldName × ShapedBased) → Bool
  | [], [] => true
  | (expectedName, expectedShape) :: expected,
      (actualName, actualShape) :: actual =>
      (expectedName == actualName) &&
        (match shapedBasedFromShape context expectedShape with
        | some shape => shapedBasedSameShape shape actualShape
        | none => false) &&
        shapedBasedFieldsMatch context expected actual
  | _, _ => false

def checkExp [BEq String] (context : Context) : Exp α → StaticResult ExpReturn
  | .const _ => staticOk { shapedBased := .word .notBased }
  | .var .local name =>
      match lookupInfo name context.locals with
      | some info => staticOk { shapedBased := info.shapedBased }
      | none => staticError (.scope ("unknown local variable: " ++ name))
  | .var .global name =>
      match lookupInfo name context.globals with
      | some info =>
          match shapedBasedFromShape context.structs info.shape with
          | some shaped => staticOk { shapedBased := shaped }
          | none => staticError (.scope ("invalid global shape: " ++ name))
      | none => staticError (.scope ("unknown global variable: " ++ name))
  | .rStruct expressions =>
      staticBind (checkExps context expressions) (fun result =>
        staticOk { shapedBased := .struct result.shapedBased })
  | .rField index value =>
      staticBind (checkExp context value) (fun result =>
        match shapedBasedFieldAt index result.shapedBased with
        | some shaped => staticOk { shapedBased := shaped }
        | none => staticError (.shape "invalid positional field index"))
  | .nStruct name fields =>
      match lookupInfo name context.structs with
      | none => staticError (.scope ("unknown struct: " ++ name))
      | some info =>
          staticBind (checkNamedExps context fields) (fun actual =>
            if shapedBasedFieldsMatch context.structs info.fields actual then
              staticOk { shapedBased := .named name actual }
            else staticError (.shape "named struct fields do not match"))
  | .nField name value =>
      staticBind (checkExp context value) (fun result =>
        match shapedBasedFieldNamed name result.shapedBased with
        | some shaped => staticOk { shapedBased := shaped }
        | none => staticError (.shape "invalid named field"))
  | .load shape address =>
      if !isWfShape context.structs shape then
        staticError (.shape "load result has an invalid shape")
      else
        staticBind (checkExp context address) (fun result =>
          if shapedBasedIsWord result.shapedBased then
            match shapedBasedFromShape context.structs shape with
            | some shaped => staticOk { shapedBased := shaped }
            | none => staticError (.scope "invalid load result shape")
          else staticError (.shape "load address is not a word"))
  | .load32 address =>
      staticBind (checkExp context address) (fun result =>
        if shapedBasedIsWord result.shapedBased then
          staticOk { shapedBased := .word .trusted }
        else staticError (.shape "load32 address is not a word"))
  | .loadByte address =>
      staticBind (checkExp context address) (fun result =>
        if shapedBasedIsWord result.shapedBased then
          staticOk { shapedBased := .word .trusted }
        else staticError (.shape "loadByte address is not a word"))
  | .op operator expressions =>
      staticBind (checkExps context expressions) (fun result =>
        let arityOk := match operator with
          | .sub => expressions.length == 2
          | _ => expressions.length >= 2
        if !arityOk then staticError (.general "invalid binary operator arity")
        else if result.shapedBased.all shapedBasedIsWord then
          staticOk { shapedBased := .word .notBased }
        else staticError (.shape "operator operand is not a word"))
  | .panOp _ expressions =>
      staticBind (checkExps context expressions) (fun result =>
        if expressions.length != 2 then staticError (.general "invalid Pancake operator arity")
        else if result.shapedBased.all shapedBasedIsWord then
          staticOk { shapedBased := .word .notBased }
        else staticError (.shape "Pancake operand is not a word"))
  | .cmp _ left right =>
      staticBind (checkExp context left) (fun leftResult =>
        staticBind (checkExp context right) (fun rightResult =>
          if shapedBasedSameShape leftResult.shapedBased rightResult.shapedBased then
            staticOk { shapedBased := .word .notBased }
          else staticError (.shape "comparison operands have different shapes")))
  | .shift _ left right =>
      staticBind (checkExp context left) (fun leftResult =>
        staticBind (checkExp context right) (fun rightResult =>
          if shapedBasedIsWord leftResult.shapedBased && shapedBasedIsWord rightResult.shapedBased then
            staticOk { shapedBased := rightResult.shapedBased }
          else staticError (.shape "shift operands are not words")))
  | .baseAddr => staticOk { shapedBased := .word .based }
  | .topAddr => staticOk { shapedBased := .word .based }
  | .bytesInWord => staticOk { shapedBased := .word .notBased }
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  checkExps [BEq String] (context : Context) : List (Exp α) → StaticResult ExpsReturn
    | [] => staticOk { shapedBased := [] }
    | expression :: expressions =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkExps context expressions) (fun rest =>
            staticOk { shapedBased := result.shapedBased :: rest.shapedBased }))
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  checkNamedExps [BEq String] (context : Context) :
      List (FieldName × Exp α) → StaticResult (List (FieldName × ShapedBased))
    | [] => staticOk []
    | (name, expression) :: fields =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkNamedExps context fields) (fun rest =>
            staticOk ((name, result.shapedBased) :: rest)))
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

end Pancake
