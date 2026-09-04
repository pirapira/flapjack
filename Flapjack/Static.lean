import Flapjack.Language

/-!
Static-checker data and shape-context operations.

This module is the executable front-end checker. It ports the reusable
pieces of CakeML's `panStatic` theory together with declaration-level
context construction and function-body validation.
-/

namespace Flapjack

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
  deriving Repr

abbrev StaticResult (α : Type u) := Except StatErr α × List StatErr

def staticResultOk (result : StaticResult α) : Bool :=
  match result.1 with
  | Except.ok _ => true
  | Except.error _ => false

def statErrMessage : StatErr → String
  | .scope message => message
  | .warning message => message
  | .general message => message
  | .shape message => message

def staticResultErrorMessage (result : StaticResult α) : Option String :=
  match result.1 with
  | Except.ok _ => none
  | Except.error error => some (statErrMessage error)

inductive Based where
  | based
  | notBased
  | trusted
  | notTrusted
  deriving Repr

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
  expectedReturn : Option Shape
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

def staticResultLocation (result : StaticResult ProgReturn) : Option String :=
  match result.1 with
  | Except.ok value => some value.currentLocation
  | Except.error _ => none

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

@[simp] theorem shapedBasedSameShape_struct_words :
    shapedBasedSameShape
      (.struct [.word .notBased, .word .notBased])
      (.struct [.word .notBased, .word .notBased]) = true := by
  rfl

def shapesSame : Shape → Shape → Bool
  | .one, .one => true
  | .comb left, .comb right => shapesSameList left right
  | .named left, .named right => left == right
  | _, _ => false
where
  shapesSameList : List Shape → List Shape → Bool
    | [], [] => true
    | left :: lefts, right :: rights => shapesSame left right && shapesSameList lefts rights
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
        if expressions.length != 2 then staticError (.general "invalid Flapjack operator arity")
        else if result.shapedBased.all shapedBasedIsWord then
          staticOk { shapedBased := .word .notBased }
        else staticError (.shape "Flapjack operand is not a word"))
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

def shapedBasedMatchesShape (context : StructContext) (shape : Shape)
    (shaped : ShapedBased) : Bool :=
  match shapedBasedFromShape context shape with
  | some expected => shapedBasedSameShape expected shaped
  | none => false

def functionArgumentsMatch (context : StructContext) :
    List (VarName × Shape) → List ShapedBased → Bool
  | [], [] => true
  | (_, shape) :: parameters, argument :: arguments =>
      shapedBasedMatchesShape context shape argument &&
        functionArgumentsMatch context parameters arguments
  | _, _ => false

def checkPrimitiveArgs [BEq String] (_context : Context) (operator : PrimOp)
    (arguments : List ShapedBased) : StaticResult ShapedBased :=
  match operator with
  | .addCarry =>
      if arguments.length != 3 then
        staticError (.general "AddCarry expects three arguments")
      else if arguments.all shapedBasedIsWord then
        staticOk (.struct [.word .notBased, .word .notBased])
      else staticError (.shape "AddCarry operand is not a word")

def progOk (last : LastStmt) (exitsFunction exitsLoop : Bool) (location : String) :
    StaticResult ProgReturn :=
  staticOk
    { exitsFunction := exitsFunction, exitsLoop := exitsLoop, last := last,
      variableDelta := [], currentLocation := location }

def checkCallDestination [BEq String] (context : Context) (returnShape : Shape)
    : Option (VarKind × VarName) → StaticResult ProgReturn
  | none => progOk .otherLast false false context.location
  | some (kind, name) =>
      match kind with
      | .local =>
          match lookupInfo name context.locals with
          | some localInfo =>
              if shapedBasedMatchesShape context.structs returnShape localInfo.shapedBased then
                progOk .otherLast false false context.location
              else staticError (.shape "call destination shape does not match")
          | none => staticError (.scope ("unknown call destination: " ++ name))
      | .global =>
          match lookupInfo name context.globals with
          | some globalInfo =>
              if shapesSame globalInfo.shape returnShape then
                progOk .otherLast false false context.location
              else staticError (.shape "global call destination shape does not match")
          | none => staticError (.scope ("unknown call destination: " ++ name))

def checkProg [BEq String] (context : Context) : Prog α → StaticResult ProgReturn
  | .skip => progOk .invisLast false false context.location
  | .dec name shape value body =>
      if !isWfShape context.structs shape then
        staticError (.shape "local declaration has an invalid shape")
      else
        staticBind (checkExp context value) (fun result =>
          if shapedBasedMatchesShape context.structs shape result.shapedBased then
            let nextContext := { context with
              locals := (name, { shapedBased := result.shapedBased }) :: context.locals }
            checkProg nextContext body
          else staticError (.shape "local declaration shape does not match"))
  | .assign .local name value =>
      match lookupInfo name context.locals with
      | none => staticError (.scope ("unknown local variable: " ++ name))
      | some info =>
          staticBind (checkExp context value) (fun result =>
            if shapedBasedSameShape info.shapedBased result.shapedBased then
              progOk .otherLast false false context.location
            else staticError (.shape "local assignment shape does not match"))
  | .assign .global name value =>
      match lookupInfo name context.globals with
      | none => staticError (.scope ("unknown global variable: " ++ name))
      | some info =>
          staticBind (checkExp context value) (fun result =>
            if shapedBasedMatchesShape context.structs info.shape result.shapedBased then
              progOk .otherLast false false context.location
            else staticError (.shape "global assignment shape does not match"))
  | .primitive name _ arguments =>
      match lookupInfo name context.locals with
      | none => staticError (.scope ("unknown primitive destination: " ++ name))
      | some destinationInfo =>
          staticBind (checkCallArgs context arguments) (fun argumentResult =>
            staticBind (checkPrimitiveArgs context .addCarry argumentResult.shapedBased)
              (fun resultShape =>
                if shapedBasedSameShape destinationInfo.shapedBased resultShape then
                  progOk .otherLast false false context.location
                else staticError (.shape "primitive result shape does not match")))
  | .store address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedIsWord addressResult.shapedBased &&
              shapedBasedIsWord valueResult.shapedBased then
            progOk .otherLast false false context.location
          else staticError (.shape "store operands are not words")))
  | .store32 address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedIsWord addressResult.shapedBased &&
              shapedBasedIsWord valueResult.shapedBased then
            progOk .otherLast false false context.location
          else staticError (.shape "store32 operands are not words")))
  | .storeByte address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedIsWord addressResult.shapedBased &&
              shapedBasedIsWord valueResult.shapedBased then
            progOk .otherLast false false context.location
          else staticError (.shape "storeByte operands are not words")))
  | .seq first second =>
      staticBind (checkProg context first) (fun firstResult =>
        if firstResult.exitsFunction then
          (Except.ok firstResult, [.warning "statement after function exit is unreachable"])
        else staticBind (checkProg
          { context with location := firstResult.currentLocation } second) (fun secondResult =>
          staticOk secondResult))
  | .ite condition thenBranch elseBranch =>
      staticBind (checkExp context condition) (fun conditionResult =>
        if shapedBasedIsWord conditionResult.shapedBased then
          staticBind (checkProg context thenBranch) (fun thenResult =>
            staticBind (checkProg
              { context with location := thenResult.currentLocation } elseBranch) (fun elseResult =>
              progOk .condExitLast
                (thenResult.exitsFunction && elseResult.exitsFunction)
                (thenResult.exitsLoop && elseResult.exitsLoop) context.location))
        else staticError (.shape "condition is not a word"))
  | .while condition body =>
      staticBind (checkExp context condition) (fun conditionResult =>
        if shapedBasedIsWord conditionResult.shapedBased then
          let loopContext := { context with inLoop := true }
          staticBind (checkProg loopContext body) (fun _ =>
            progOk .otherLast false false context.location)
        else staticError (.shape "while condition is not a word"))
  | .break =>
      if context.inLoop then progOk .breakLast false true context.location
      else staticError (.general "break used outside a loop")
  | .continue =>
      if context.inLoop then progOk .contLast false true context.location
      else staticError (.general "continue used outside a loop")
  | .call info function arguments =>
      match lookupInfo function context.functions with
      | none => staticError (.scope ("unknown function: " ++ function))
      | some functionInfo =>
          let returnShape := functionInfo.returnShape
          staticBind (checkCallArgs context arguments) (fun argumentResult =>
            if !functionArgumentsMatch context.structs functionInfo.params argumentResult.shapedBased then
              staticError (.shape "function argument shapes do not match")
            else
              match info with
              | none => progOk .tailLast true false context.location
              | some (destination, none) => checkCallDestination context returnShape destination
              | some (destination, some (exception, handlerVariable, handlerProgram)) =>
                  match lookupInfo exception context.exceptions,
                      lookupInfo handlerVariable context.locals with
                  | none, _ => staticError (.scope ("unknown exception: " ++ exception))
                  | _, none => staticError (.scope
                      ("unknown exception handler variable: " ++ handlerVariable))
                  | some exceptionShape, some handlerInfo =>
                      if !shapedBasedMatchesShape context.structs exceptionShape
                          handlerInfo.shapedBased then
                        staticError (.shape "exception handler variable shape does not match")
                      else
                        let handlerShaped :=
                          (shapedBasedFromShape context.structs exceptionShape).getD
                            handlerInfo.shapedBased
                        let handlerContext := { context with locals :=
                          (handlerVariable, { shapedBased := handlerShaped }) :: context.locals }
                        staticBind (checkProg handlerContext handlerProgram) (fun _ =>
                          checkCallDestination context returnShape destination))
  | .decCall name shape function arguments body =>
      if (lookupInfo name context.locals).isSome ||
          (lookupInfo name context.globals).isSome then
        staticError (.scope ("local declaration redeclares: " ++ name))
      else if !isWfShape context.structs shape then
        staticError (.shape "declaration-call result has an invalid shape")
      else
        match lookupInfo function context.functions with
        | none => staticError (.scope ("unknown function: " ++ function))
        | some functionInfo =>
            staticBind (checkCallArgs context arguments) (fun argumentResult =>
              if !functionArgumentsMatch context.structs functionInfo.params
                  argumentResult.shapedBased then
                staticError (.shape "function argument shapes do not match")
              else if !shapesSame shape functionInfo.returnShape then
                staticError (.shape "declaration-call result shape does not match")
              else
                match shapedBasedFromShape context.structs shape with
                | none => staticError (.scope "invalid declaration-call result shape")
                | some shaped =>
                    let nextContext := { context with locals :=
                      (name, { shapedBased := shaped }) :: context.locals }
                    staticBind (checkProg nextContext body) (fun result =>
                      staticOk { result with variableDelta := [] }))
  | .extCall function configuration configurationLength array arrayLength =>
      staticBind (checkCallArgs context
        [configuration, configurationLength, array, arrayLength])
        (fun argumentResult =>
          if argumentResult.shapedBased.all
              (shapedBasedMatchesShape context.structs .one) then
            progOk .otherLast false false context.location
          else staticError (.shape ("foreign-call argument is not a word: " ++ function)))
  | .raise exception value =>
      match lookupInfo exception context.exceptions with
      | none => staticError (.scope ("unknown exception: " ++ exception))
      | some shape =>
          staticBind (checkExp context value) (fun result =>
            if shapedBasedMatchesShape context.structs shape result.shapedBased then
              progOk .raiseLast true false context.location
            else staticError (.shape "raised exception value has the wrong shape"))
  | .return value =>
      staticBind (checkExp context value) (fun result =>
        match context.expectedReturn with
        | none => progOk .retLast true false context.location
        | some shape =>
            if shapedBasedMatchesShape context.structs shape result.shapedBased then
              progOk .retLast true false context.location
            else
              staticError (.shape "return expression has the wrong shape"))
  | .shMemLoad _ _ name address =>
      match lookupInfo name context.locals with
      | none => staticError (.scope ("unknown shared-memory destination: " ++ name))
      | some _ =>
          staticBind (checkExp context address) (fun result =>
            if shapedBasedIsWord result.shapedBased then
              progOk .otherLast false false context.location
            else staticError (.shape "shared-memory address is not a word"))
  | .shMemStore _ address value =>
      staticBind (checkExp context address) (fun addressResult =>
        staticBind (checkExp context value) (fun valueResult =>
          if shapedBasedIsWord addressResult.shapedBased &&
              shapedBasedIsWord valueResult.shapedBased then
            progOk .otherLast false false context.location
          else staticError (.shape "shared-memory operands are not words")))
  | .tick => progOk .otherLast false false context.location
  | .annot tag text =>
      let location := if tag == "location" then "AT " ++ text ++ ": " else context.location
      progOk .invisLast false false location
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  checkCallArgs [BEq String] (context : Context) :
      List (Exp α) → StaticResult ExpsReturn
    | [] => staticOk { shapedBased := [] }
    | expression :: expressions =>
        staticBind (checkExp context expression) (fun result =>
          staticBind (checkCallArgs context expressions) (fun rest =>
            staticOk { shapedBased := result.shapedBased :: rest.shapedBased }))
  termination_by expressions => sizeOf expressions
    decreasing_by
      all_goals first | sizeOf_list_dec | decreasing_trivial

def firstRepeat [BEq α] : List α → Option α
  | [] => none
  | value :: values =>
      if values.any (fun candidate => candidate == value) then some value
      else firstRepeat values

def checkShape [BEq String] (context : StructContext) (shape : Shape) :
    StaticResult Unit :=
  if isWfShape context shape then
    staticOk ()
  else
    staticError (.scope "shape refers to an unknown or invalid structure")

def checkShapeFields [BEq String] (context : StructContext)
    (fields : List (FieldName × Shape)) : StaticResult Unit :=
  if isWfFields context fields then
    staticOk ()
  else
    staticError (.scope "structure field has an unknown or invalid shape")

def localInfosFromParams [BEq String] (context : StructContext) :
    List (VarName × Shape) → InfoMap LocalInfo
  | [] => []
  | (name, shape) :: params =>
      let shaped := (shapedBasedFromShape context shape).getD (.word .trusted)
      (name, { shapedBased := shaped }) :: localInfosFromParams context params

structure StaticDeclContext where
  functions : InfoMap FuncInfo
  globals : InfoMap GlobalInfo
  exceptions : InfoMap Shape
  deriving Repr

def staticCheckNames [BEq String] (context : StructContext) :
    List (Decl α) → StaticResult StructContext
  | [] => staticOk context
  | .name name fields :: declarations =>
      if (lookupInfo name context).isSome then
        staticError (.scope ("structure is redeclared: " ++ name))
      else
        match firstRepeat (fields.map Prod.fst) with
        | some field =>
            staticError (.scope ("structure field is redeclared: " ++ field))
        | none =>
            staticBind (checkShapeFields context fields) (fun _ =>
              let info : StructInfo :=
                { fields := fields
                  size := shapeSizeWithContext context (.comb (fields.map Prod.snd)) }
              staticBind (staticCheckNames ((name, info) :: context) declarations)
                (fun result => staticOk result))
  | _ :: declarations => staticCheckNames context declarations
termination_by declarations => sizeOf declarations

def staticCheckFunctionHeader [BEq String] (context : StructContext)
    (declaration : FunDecl α) : StaticResult Unit :=
  if declaration.name = "main" then
    if !declaration.params.isEmpty then
      staticError (.general "main function has arguments")
    else if declaration.exported then
      staticError (.general "main function is exported")
    else if !shapesSame declaration.returnShape .one then
      staticError (.shape "main function must return one word")
    else
      staticOk ()
  else if (firstRepeat (declaration.params.map Prod.fst)).isSome then
    staticError (.scope ("function parameter is redeclared: " ++ declaration.name))
  else if declaration.exported && declaration.params.length > 4 then
    staticError (.general ("exported function has more than four arguments: " ++
      declaration.name))
  else if declaration.exported &&
      !declaration.params.all (fun (_, shape) => shapesSame shape .one) then
    staticError (.shape "exported function parameters must be words")
  else if declaration.exported && !shapesSame declaration.returnShape .one then
    staticError (.shape "exported function must return one word")
  else if !isWfShape context declaration.returnShape ||
      !declaration.params.all (fun (_, shape) => isWfShape context shape) then
    staticError (.shape ("function has an unknown or invalid parameter/return shape: " ++
      declaration.name))
  else if shapeSizeWithContext context declaration.returnShape > 32 then
    staticError (.shape ("function returns more than 32 words: " ++ declaration.name))
  else
    staticOk ()

def staticCheckDecls [BEq String] (structs : StructContext) :
    StaticDeclContext → List (Decl α) → StaticResult StaticDeclContext
  | context, [] => staticOk context
  | context, .name _ _ :: declarations =>
      staticCheckDecls structs context declarations
  | context, .exnDecl exception shape :: declarations =>
      if (lookupInfo exception context.exceptions).isSome then
        staticError (.scope ("exception is redeclared: " ++ exception))
      else
        staticBind (checkShape structs shape) (fun _ =>
          staticCheckDecls structs
            { context with exceptions := (exception, shape) :: context.exceptions }
            declarations)
  | context, .decl shape name value :: declarations =>
      if (lookupInfo name context.globals).isSome then
        staticError (.scope ("global variable is redeclared: " ++ name))
      else
        staticBind (checkShape structs shape) (fun _ =>
          let checkingContext : Context :=
            { locals := []
              globals := context.globals
              functions := []
              expectedReturn := none
              exceptions := context.exceptions
              structs := structs
              scope := .declScope name
              inLoop := false
              reachable := .isReach
              last := .invisLast
              location := "" }
          staticBind (checkExp checkingContext value) (fun result =>
            if shapedBasedMatchesShape structs shape result.shapedBased then
              staticCheckDecls structs
                { context with globals := (name, { shape := shape }) :: context.globals }
                declarations
            else
              staticError (.shape ("global initializer has the wrong shape: " ++ name))))
  | context, .function declaration :: declarations =>
      if (lookupInfo declaration.name context.functions).isSome then
        staticError (.scope ("function is redeclared: " ++ declaration.name))
      else
        staticBind (staticCheckFunctionHeader structs declaration) (fun _ =>
          staticCheckDecls structs
            { context with functions :=
                (declaration.name,
                  { returnShape := declaration.returnShape
                    params := declaration.params }) :: context.functions }
            declarations)
termination_by _ declarations => declarations.length
decreasing_by
  all_goals decreasing_trivial

def staticCheckProgs [BEq String] (structs : StructContext)
    (context : StaticDeclContext) : List (Decl α) → StaticResult Unit
  | [] => staticOk ()
  | .function declaration :: declarations =>
      let checkingContext : Context :=
        { locals := localInfosFromParams structs declaration.params
          globals := context.globals
          functions := context.functions
          expectedReturn := some declaration.returnShape
          exceptions := context.exceptions
          structs := structs
          scope := .funScope declaration.name ""
          inLoop := false
          reachable := .isReach
          last := .invisLast
          location := "" }
      staticBind (checkProg checkingContext declaration.body) (fun result =>
        if result.exitsFunction then
          staticCheckProgs structs context declarations
        else
          staticError (.general ("missing return statement in function: " ++
            declaration.name)))
  | _ :: declarations => staticCheckProgs structs context declarations
termination_by declarations => declarations.length

def staticCheck [BEq String] (declarations : List (Decl α)) : StaticResult Unit :=
  staticBind (staticCheckNames (α := α) [] declarations) (fun structs =>
    staticBind (staticCheckDecls structs
      { functions := [], globals := [], exceptions := [] } declarations)
      (fun context => staticCheckProgs structs context declarations))

end Flapjack
