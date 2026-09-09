import Flapjack.PanStructs

/-!
The core of Pancake's `pan_globals` pass.

Global values are laid out in the heap from `TopAddr`. This module keeps the
word representation abstract and receives the natural-number-to-word map in
the context, allowing the same executable pass to be instantiated with
`BitVec` for the RISC-V backend or with `Nat` in small tests.
-/

namespace Flapjack

structure GlobalPassContext (α : Type u) where
  globals : InfoMap (Shape × α)
  globalsSize : α
  maxGlobalsSize : α
  bytesInWord : α
  fromNat : Nat → α

structure GlobalCompiledProgram (α : Type u) where
  initializers : List (Prog α)
  declarations : List (Decl α)
  context : GlobalPassContext α

def globalAddress [Add α] [Mul α] (context : GlobalPassContext α) (shape : Shape) : α :=
  context.globalsSize + context.bytesInWord * context.fromNat (Shape.shapeSize shape)

def globalCompileExp [BEq String] (context : GlobalPassContext α) : Exp α → Exp α
  | .var .local name => .var .local name
  | .var .global name =>
      match lookupInfo name context.globals with
      | some (shape, address) =>
          .load shape (.op .sub [.topAddr, .const address])
      | none => .const (context.fromNat 0)
  | .rStruct expressions => .rStruct (globalCompileExps context expressions)
  | .rField index expression => .rField index (globalCompileExp context expression)
  | .nStruct _ _ => .const (context.fromNat 0)
  | .nField _ _ => .const (context.fromNat 0)
  | .load shape address => .load shape (globalCompileExp context address)
  | .load32 address => .load32 (globalCompileExp context address)
  | .loadByte address => .loadByte (globalCompileExp context address)
  | .op operator expressions => .op operator (globalCompileExps context expressions)
  | .panOp operator expressions => .panOp operator (globalCompileExps context expressions)
  | .cmp operator left right =>
      .cmp operator (globalCompileExp context left) (globalCompileExp context right)
  | .shift operator left right =>
      .shift operator (globalCompileExp context left) (globalCompileExp context right)
  | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
  | expression => expression
termination_by expression => sizeOf expression
where
  globalCompileExps [BEq String] (context : GlobalPassContext α) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        globalCompileExp context expression :: globalCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalExpVars : Exp α → List VarName
  | .const _ => []
  | .var _ name => [name]
  | .rStruct fields => globalExpVarsList fields
  | .rField _ value => globalExpVars value
  | .nStruct _ fields => globalExpVarsFieldList fields
  | .nField _ value => globalExpVars value
  | .load _ address => globalExpVars address
  | .load32 address => globalExpVars address
  | .loadByte address => globalExpVars address
  | .op _ arguments => globalExpVarsList arguments
  | .panOp _ arguments => globalExpVarsList arguments
  | .cmp _ left right => globalExpVars left ++ globalExpVars right
  | .shift _ left right => globalExpVars left ++ globalExpVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []
termination_by expression => sizeOf expression
where
  globalExpVarsList : List (Exp α) → List VarName
    | [] => []
    | expression :: expressions => globalExpVars expression ++ globalExpVarsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  globalExpVarsFieldList : List (FieldName × Exp α) → List VarName
    | [] => []
    | (_, expression) :: fields => globalExpVars expression ++ globalExpVarsFieldList fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalCompileExpList [BEq String] (context : GlobalPassContext α) :
    List (Exp α) → List (Exp α)
  | [] => []
  | expression :: expressions =>
      globalCompileExp context expression :: globalCompileExpList context expressions
termination_by expressions => sizeOf expressions
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalFreeVars : Prog α → List VarName
  | .skip => []
  | .dec name _ value body =>
      globalExpVars value ++ (globalFreeVars body).filter (· != name)
  | .assign kind name value =>
      (if kind == .local then [name] else []) ++ globalExpVars value
  | .primitive name _ arguments => name :: arguments.flatMap globalExpVars
  | .store address value => globalExpVars address ++ globalExpVars value
  | .store32 address value => globalExpVars address ++ globalExpVars value
  | .storeByte address value => globalExpVars address ++ globalExpVars value
  | .seq first second => globalFreeVars first ++ globalFreeVars second
  | .ite condition thenBranch elseBranch =>
      globalExpVars condition ++ globalFreeVars thenBranch ++ globalFreeVars elseBranch
  | .while condition body => globalExpVars condition ++ globalFreeVars body
  | .break => []
  | .continue => []
  | .call info _ arguments =>
      let destination := match info with
        | some (some (kind, name), _) => if kind == .local then [name] else []
        | _ => []
      let handler := match info with
        | some (_, some (_, handlerVar, program)) => handlerVar :: globalFreeVars program
        | _ => []
      destination ++ handler ++ arguments.flatMap globalExpVars
  | .decCall name _ _ arguments body =>
      name :: globalFreeVars body ++ arguments.flatMap globalExpVars
  | .extCall _ configuration configurationLength array arrayLength =>
      globalExpVars configuration ++ globalExpVars configurationLength ++
        globalExpVars array ++ globalExpVars arrayLength
  | .raise _ value => globalExpVars value
  | .return value => globalExpVars value
  | .shMemLoad _ kind name address =>
      (if kind == .local then [name] else []) ++ globalExpVars address
  | .shMemStore _ address value => globalExpVars address ++ globalExpVars value
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program

def globalApostrophes : Nat → String
  | 0 => ""
  | count + 1 => "'" ++ globalApostrophes count

def globalFreshNameAux [BEq String] (name : String) (names : List String) :
    Nat → Nat → String
  | candidate, 0 => name ++ globalApostrophes candidate
  | candidate, fuel + 1 =>
      let candidateName := name ++ globalApostrophes candidate
      if names.contains candidateName then
        globalFreshNameAux name names (candidate + 1) fuel
      else candidateName

def globalFreshName [BEq String] (name : String) (names : List String) : String :=
  globalFreshNameAux name names 0 names.length

def globalShapeVal (context : GlobalPassContext α) : Shape → Exp α
  | .one => .const (context.fromNat 0)
  | .named _ => .const (context.fromNat 0)
  | .comb shapes => .rStruct (shapes.map (globalShapeVal context))
termination_by shape => sizeOf shape

def globalCompileProg [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape (globalCompileExp context value)
        (globalCompileProg context body)
  | .assign .global name value =>
      match lookupInfo name context.globals with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value)
      | none => .skip
  | .assign .local name value =>
      .assign .local name (globalCompileExp context value)
  | .primitive name operator arguments =>
      .primitive name operator (globalCompileExpList context arguments)
  | .store address value =>
      .store (globalCompileExp context address) (globalCompileExp context value)
  | .store32 address value =>
      .store32 (globalCompileExp context address) (globalCompileExp context value)
  | .storeByte address value =>
      .storeByte (globalCompileExp context address) (globalCompileExp context value)
  | .seq first second =>
      .seq (globalCompileProg context first) (globalCompileProg context second)
  | .ite condition thenBranch elseBranch =>
      .ite (globalCompileExp context condition)
        (globalCompileProg context thenBranch) (globalCompileProg context elseBranch)
  | .while condition body =>
      .while (globalCompileExp context condition) (globalCompileProg context body)
  | .call info function arguments =>
      let compiledArguments := globalCompileExpList context arguments
      match info with
        | none => .call none function compiledArguments
        | some (none, none) =>
            .call (some (none, none)) function compiledArguments
        | some (none, some (exception, handlerVar, handler)) =>
            .call (some (none, some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.local, name), none) =>
            .call (some (some (.local, name), none)) function compiledArguments
        | some (some (.local, name), some (exception, handlerVar, handler)) =>
            .call (some (some (.local, name), some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.global, name), none) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                .decCall "" shape function compiledArguments
                  (.store (.op .sub [.topAddr, .const address])
                    (.var .local ""))
            | none =>
                .call (some (none, none)) function compiledArguments
        | some (some (.global, name), some (exception, handlerVar, handler)) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                let compiledHandlerProgram := globalCompileProg context handler
                let names := handlerVar :: globalFreeVars compiledHandlerProgram ++
                  compiledArguments.flatMap globalExpVars
                let resultName := globalFreshName "" names
                let flagName := globalFreshName resultName (resultName :: names)
                let handlerBody :=
                  .seq compiledHandlerProgram
                    (.assign .local flagName (.const (context.fromNat 1)))
                let callInfo := some (some (.local, resultName),
                  some (exception, handlerVar, handlerBody))
                let callProgram : Prog α :=
                  .call callInfo function compiledArguments
                let storeAddress : Exp α :=
                  .op .sub [.topAddr, .const address]
                .dec resultName shape (globalShapeVal context shape)
                  (.dec flagName .one (.const (context.fromNat 0))
                    (.seq callProgram
                      (.ite (.var .local flagName) .skip
                        (.store storeAddress
                          (.var .local resultName)))))
            | none =>
                .call (some (none, some (exception, handlerVar,
                  globalCompileProg context handler))) function compiledArguments
  | .decCall name shape function arguments body =>
      .decCall name shape function (globalCompileExpList context arguments)
        (globalCompileProg context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (globalCompileExp context configuration)
        (globalCompileExp context configurationLength) (globalCompileExp context array)
        (globalCompileExp context arrayLength)
  | .raise exception value => .raise exception (globalCompileExp context value)
  | .return value => .return (globalCompileExp context value)
  | .shMemLoad size kind name address =>
      match kind, lookupInfo name context.globals with
      | .local, _ =>
          .shMemLoad size .local name (globalCompileExp context address)
      | .global, some (.one, globalAddress) =>
          let localName := name ++ globalApostrophes 1
          .dec name .one (globalCompileExp context address)
            (.dec localName .one (.const (context.fromNat 0))
              (.seq
                (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress])
                  (.var .local localName))))
      | .global, _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (globalCompileExp context address) (globalCompileExp context value)
  | program => program
termination_by program => sizeOf program

/-! The declaration-order and function-permutation helpers used by
    CakeML's `pan_to_target`.  Keeping these transformations separate from
    global allocation makes their name-preservation contracts reusable by the
    target-facing pipeline. -/

def globalRenameFunctionName [BEq String]
    (source target name : FunName) : FunName :=
  if source == name then target else if target == name then source else name

def globalRenameProg [BEq String]
    (source target : FunName) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape value (globalRenameProg source target body)
  | .seq first second =>
      .seq (globalRenameProg source target first) (globalRenameProg source target second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (globalRenameProg source target thenBranch)
        (globalRenameProg source target elseBranch)
  | .while condition body =>
      .while condition (globalRenameProg source target body)
  | .call info function arguments =>
      let renamedInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar,
              globalRenameProg source target handler))
      .call renamedInfo (globalRenameFunctionName source target function) arguments
  | .decCall name shape function arguments body =>
      .decCall name shape (globalRenameFunctionName source target function) arguments
        (globalRenameProg source target body)
  | program => program
termination_by program => sizeOf program

def globalRenameDecls [BEq String]
    (source target : FunName) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with
        name := globalRenameFunctionName source target declaration.name
        body := globalRenameProg source target declaration.body } ::
        globalRenameDecls source target declarations
  | declaration :: declarations =>
      declaration :: globalRenameDecls source target declarations
termination_by declarations => sizeOf declarations

def globalFunctionNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      declaration.name :: globalFunctionNames declarations
  | _ :: declarations => globalFunctionNames declarations
termination_by declarations => sizeOf declarations

def globalDeclsFilter (predicate : Decl α → Bool) : List (Decl α) → List (Decl α)
  | [] => []
  | declaration :: declarations =>
      if predicate declaration then
        declaration :: globalDeclsFilter predicate declarations
      else globalDeclsFilter predicate declarations
termination_by declarations => sizeOf declarations

def globalDeclIsName : Decl α → Bool
  | .name _ _ => true
  | _ => false

def globalDeclIsException : Decl α → Bool
  | .exnDecl _ _ => true
  | _ => false

def globalDeclIsGlobal : Decl α → Bool
  | .decl _ _ _ => true
  | _ => false

def globalDeclIsFunction : Decl α → Bool
  | .function _ => true
  | _ => false

def globalResortDecls (declarations : List (Decl α)) : List (Decl α) :=
  globalDeclsFilter globalDeclIsName declarations ++
    globalDeclsFilter globalDeclIsException declarations ++
    globalDeclsFilter globalDeclIsGlobal declarations ++
    globalDeclsFilter globalDeclIsFunction declarations

def globalNewMainName [BEq String] (declarations : List (Decl α)) : FunName :=
  globalFreshName "main" (globalFunctionNames declarations)

def globalCollect [Add α] [Mul α] (context : GlobalPassContext α) :
    List (Decl α) → GlobalPassContext α
  | [] => context
  | .decl shape name _ :: declarations =>
      let address := globalAddress context shape
      globalCollect { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } declarations
  | _ :: declarations => globalCollect context declarations

def globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := globalCompileProg context declaration.body } ::
        globalCompileDecls context declarations
  | .exnDecl exception shape :: declarations =>
      .exnDecl exception shape :: globalCompileDecls context declarations
  | _ :: declarations => globalCompileDecls context declarations

def globalCompileInitializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Prog α)
  | [] => []
  | .decl _shape name value :: declarations =>
      let initializer :=
        match lookupInfo name context.globals with
        | some (_, address) =>
            .store (.op .sub [.topAddr, .const address])
              (globalCompileExp context value)
        | none => .skip
      initializer :: globalCompileInitializers context declarations
  | _ :: declarations => globalCompileInitializers context declarations

def globalCompileTop [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α)) :
    GlobalCompiledProgram α :=
  let initial : GlobalPassContext α :=
    { globals := []
      globalsSize := fromNat 0
      maxGlobalsSize := fromNat 0
      bytesInWord := bytesInWord
      fromNat := fromNat }
  let collected := globalCollect initial declarations
  let context := { collected with maxGlobalsSize := collected.globalsSize }
  { initializers := globalCompileInitializers context declarations
    declarations := globalCompileDecls context declarations
    context := context }

@[simp] theorem globalCompileExp_local [BEq String]
    (context : GlobalPassContext α) (name : VarName) :
    globalCompileExp context (.var .local name) = .var .local name := by
  simp [globalCompileExp]

theorem globalCompileExp_global [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (name : VarName) (shape : Shape) (address : α)
    (lookup : lookupInfo name context.globals = some (shape, address)) :
    globalCompileExp context (.var .global name) =
      .load shape (.op .sub [.topAddr, .const address]) := by
  simp [globalCompileExp, lookup]

theorem globalCompileProg_seq [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (first second : Prog α) :
    globalCompileProg context (.seq first second) =
      .seq (globalCompileProg context first) (globalCompileProg context second) := by
  simp [globalCompileProg]

theorem globalCollect_decl [Add α] [Mul α]
    (context : GlobalPassContext α) (shape : Shape) (name : String)
    (value : Exp α) :
    (globalCollect context [.decl shape name value]).globalsSize =
      globalAddress context shape := by
  simp [globalCollect]

end Flapjack
