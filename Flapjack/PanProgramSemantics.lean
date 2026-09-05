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
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : PanValueProgramState α) :
    List (Decl α) → Option (PanValueProgramState α)
  | [] => some state
  | .name name fields :: declarations =>
      if (lookupInfo name state.structs).isSome then none
      else if !(fields.map (fun field => field.1)).Nodup then none
      else if !fields.all (fun field => isWfShape state.structs field.2) then none
      else
        let info := panValueDeclStructInfo state.structs fields
        evalPanValueDeclarations
          { state with structs := (name, info) :: state.structs } declarations
  | .decl shape name expression :: declarations => do
      let value ← evalPanValueExp state.structs (fun _ => none) state.globals
        state.memory state.baseAddress state.topAddress state.bytesInWord expression
      if panShapeMatches (panValueShape state.structs value) shape then
        evalPanValueDeclarations
          { state with globals := updatePanValueMap state.globals name value } declarations
      else none
  | .function declaration :: declarations =>
      if declaration.params.all (fun parameter => isWfShape state.structs parameter.2) &&
          isWfShape state.structs declaration.returnShape then
        evalPanValueDeclarations
          { state with functions :=
              (declaration.name, declaration.params.map (fun parameter => parameter.1),
                declaration.body) :: state.functions } declarations
      else none
  | .exnDecl exception shape :: declarations =>
      if (lookupInfo exception state.exceptions).isSome then none
      else if isWfShape state.structs shape then
        evalPanValueDeclarations
          { state with exceptions := (exception, shape) :: state.exceptions } declarations
      else none
termination_by declarations => sizeOf declarations

def evalPanValueProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    Option (PanValueControlResult α) := do
  let state ← evalPanValueDeclarations initial declarations
  evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory none entry arguments

def panValueProgramResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    Option (List (PanValue α)) :=
  (evalPanValueProgram initial primitive ffi fuel declarations entry arguments).bind
    (fun result => match result with
    | .returned _ _ _ values => some values
    | _ => none)

theorem evalPanValueDeclarations_empty
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (state : PanValueProgramState α) :
    evalPanValueDeclarations state [] = some state := by
  simp [evalPanValueDeclarations]

end Flapjack
