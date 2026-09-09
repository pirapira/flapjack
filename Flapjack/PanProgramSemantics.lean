import Flapjack.PanMemory

/-!
Top-level structured Pancake semantics.

`PanValues` already contains the fuel-bounded expression and control-result
evaluator, but callers previously had to construct the function table and
global environment by hand.  CakeML's `evaluate_decls` builds those
environments from declarations before evaluating the selected entry point.
This module ports that boundary while retaining explicit host handlers for
primitive and foreign calls.
-/

namespace Flapjack

structure PanValueProgramState (α : Type u) where
  structs : StructContext
  globals : VarName → Option (PanValue α)
  functions : List (FunName × List VarName × Prog α)
  returnShapes : InfoMap Shape
  exceptions : InfoMap Shape
  memory : α → Option (PanValue α)
  baseAddress : α
  topAddress : α
  bytesInWord : α

def panValueDeclStructInfo (context : StructContext)
    (fields : List (FieldName × Shape)) : StructInfo :=
  { fields := fields
    size := shapeSizeWithContext context (.comb (fields.map Prod.snd)) }

def evalPanValueDeclarations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : PanValueProgramState α) :
    (declarations : List (Decl α)) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      Option (PanValueProgramState α)
  | [], _ => some state
  | .name name fields :: declarations, memoryAccess =>
      if (lookupInfo name state.structs).isSome then none
      else if !(fields.map (fun field => field.1)).Nodup then none
      else if !fields.all (fun field => isWfShape state.structs field.2) then none
      else
        let info := panValueDeclStructInfo state.structs fields
        evalPanValueDeclarations
          { state with structs := (name, info) :: state.structs } declarations
          (memoryAccess := memoryAccess)
  | .decl shape name expression :: declarations, memoryAccess => do
      let value ← evalPanValueExp state.structs (fun _ => none) state.globals
        state.memory state.baseAddress state.topAddress state.bytesInWord expression
        (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape state.structs value) shape then
        evalPanValueDeclarations
          { state with globals := updatePanValueMap state.globals name value } declarations
          (memoryAccess := memoryAccess)
      else none
  | .function declaration :: declarations, memoryAccess =>
      if declaration.params.all (fun parameter => isWfShape state.structs parameter.2) &&
          isWfShape state.structs declaration.returnShape then
        let state := { state with functions :=
          (declaration.name, declaration.params.map Prod.fst,
            declaration.body) :: state.functions }
        evalPanValueDeclarations
          { state with returnShapes := (declaration.name, declaration.returnShape) ::
              state.returnShapes } declarations (memoryAccess := memoryAccess)
      else none
  | .exnDecl exception shape :: declarations, memoryAccess =>
      if (lookupInfo exception state.exceptions).isSome then none
      else if isWfShape state.structs shape then
        evalPanValueDeclarations
          { state with exceptions := (exception, shape) :: state.exceptions } declarations
          (memoryAccess := memoryAccess)
      else none
termination_by declarations => sizeOf declarations

def evalPanValueProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) :
    Option (PanValueControlResult α) := do
  let state ← evalPanValueDeclarations initial declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions)
  let result ← evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, .returned locals globals memory [value] =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory [value])
      else none
  | some _, .returned _ _ _ _ => none
  | _, result => some result

def panValueProgramResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (PanValue α)) :=
  (evalPanValueProgram initial primitive ffi fuel declarations entry arguments
    (memoryAccess := memoryAccess)).bind
    (fun result => match result with
    | .returned _ _ _ values => some values
    | _ => none)

theorem evalPanValueDeclarations_empty
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : PanValueProgramState α) :
    evalPanValueDeclarations state [] = some state := by
  simp [evalPanValueDeclarations]

end Flapjack
