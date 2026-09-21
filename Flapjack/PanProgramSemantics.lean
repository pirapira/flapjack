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
  parameterShapes : InfoMap (List (VarName × Shape)) := []
  exceptions : InfoMap Shape
  memory : α → Option (PanValue α)
  baseAddress : α
  topAddress : α
  bytesInWord : α

def panValueDeclStructInfo (context : StructContext)
    (fields : List (FieldName × Shape)) : StructInfo :=
  { fields := fields
    size := shapeSizeWithContext context (.comb (fields.map Prod.snd)) }

/-! CakeML's `decs_stcnames` pass collects and validates every struct
    declaration before evaluating any other declaration.  In particular, a
    function or global initializer may refer to a struct declared later in the
    source list.  Fields may refer only to structs preceding their own
    declaration, while all non-struct declarations see the completed context. -/
def collectPanValueStructs : List (Decl α) → StructContext → Option StructContext
  | [], context => some context
  | .name name fields :: declarations, context =>
      if (lookupInfo name context).isSome then none
      else if !(fields.map (fun field => field.1)).Nodup then none
      else if !fields.all (fun field => isWfShape context field.2) then none
      else
        collectPanValueStructs
          declarations ((name, panValueDeclStructInfo context fields) :: context)
  | _ :: declarations, context => collectPanValueStructs declarations context
termination_by declarations => sizeOf declarations

def evalPanValueDeclarationsWithStructs
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α) :
    (declarations : List (Decl α)) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      Option (PanValueProgramState α)
  | [], _ => some state
  | .name _ _ :: declarations, memoryAccess =>
      evalPanValueDeclarationsWithStructs structs state declarations
        (memoryAccess := memoryAccess)
  | .decl shape name expression :: declarations, memoryAccess => do
      let value ← evalPanValueExp structs (fun _ => none) state.globals
        state.memory state.baseAddress state.topAddress state.bytesInWord expression
        (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape structs value) shape then
        evalPanValueDeclarationsWithStructs structs
          { state with
              structs := structs
              globals := updatePanValueMap state.globals name value } declarations
          (memoryAccess := memoryAccess)
      else none
  | .function declaration :: declarations, memoryAccess =>
      /- CakeML's `evaluate_decls` installs functions without a distinctness
         check on parameter names; `ALL_DISTINCT` is only enforced per call
         in `lookup_code` (`panSemScript.sml:827-831,461-463`). -/
      if declaration.params.all (fun parameter => isWfShape structs parameter.2) &&
        isWfShape structs declaration.returnShape then
        let state := { state with functions :=
          (declaration.name, declaration.params.map Prod.fst,
            declaration.body) :: state.functions }
        evalPanValueDeclarationsWithStructs structs
          { state with
              structs := structs
              returnShapes := (declaration.name, declaration.returnShape) :: state.returnShapes
              parameterShapes := (declaration.name, declaration.params) :: state.parameterShapes }
          declarations (memoryAccess := memoryAccess)
      else none
  | .exnDecl exception shape :: declarations, memoryAccess =>
      if (lookupInfo exception state.exceptions).isSome then none
      else if isWfShape structs shape then
        evalPanValueDeclarationsWithStructs structs
          { state with
              structs := structs
              exceptions := (exception, shape) :: state.exceptions } declarations
          (memoryAccess := memoryAccess)
      else none
termination_by declarations => sizeOf declarations

def evalPanValueDeclarations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : PanValueProgramState α) :
    (declarations : List (Decl α)) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      Option (PanValueProgramState α)
  | declarations, memoryAccess => do
      let structs ← collectPanValueStructs declarations state.structs
      evalPanValueDeclarationsWithStructs structs
        { state with structs := structs } declarations
        (memoryAccess := memoryAccess)

/-- Cake's `evaluate_decls_append`
    (`cakeml/pancake/semantics/panPropsScript.sml:1540`): evaluating a
    concatenated declaration list is the sequential composition of evaluating
    each part in turn. -/
theorem evalPanValueDeclarationsWithStructs_append
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations rest : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state (declarations ++ rest)
        memoryAccess =
      (match evalPanValueDeclarationsWithStructs structs state declarations
          memoryAccess with
       | some state' =>
           evalPanValueDeclarationsWithStructs structs state' rest memoryAccess
       | none => none) := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs]
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          rw [List.cons_append]
          simp only [evalPanValueDeclarationsWithStructs]
          exact ih state
      | decl shape name expression =>
          rw [List.cons_append]
          simp only [evalPanValueDeclarationsWithStructs]
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hmatch, ih]
              · simp [hmatch]
      | function declaration =>
          rw [List.cons_append]
          simp only [evalPanValueDeclarationsWithStructs]
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf]
            exact ih _
          · simp [hwf]
      | exnDecl exception shape =>
          rw [List.cons_append]
          simp only [evalPanValueDeclarationsWithStructs]
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists]
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf]
              exact ih _
            · simp [hexists, hwf]

/-- Cake's `evaluate_decl_commute`
    (`cakeml/pancake/semantics/panPropsScript.sml:1472`): a function
    declaration commutes past a global declaration, because the function's
    well-formedness check depends only on the struct context while the global
    initializer reads only globals and memory. -/
theorem evalPanValueDeclarationsWithStructs_function_decl_commute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declaration : FunDecl α) (shape : Shape) (name : DeclarationName)
    (expression : Exp α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state
        (.function declaration :: .decl shape name expression :: declarations)
        memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.decl shape name expression :: .function declaration :: declarations)
        memoryAccess := by
  simp only [evalPanValueDeclarationsWithStructs]
  cases hval : evalPanValueExp structs (fun _ => none) state.globals
      state.memory state.baseAddress state.topAddress state.bytesInWord
      expression (memoryAccess := memoryAccess) with
  | none => simp
  | some value =>
      by_cases hmatch :
          panShapeMatches (panValueShape structs value) shape = true
      · by_cases hwf : (declaration.params.all
            (fun parameter => isWfShape structs parameter.2) &&
          isWfShape structs declaration.returnShape) = true
        · simp [hmatch, hwf]
        · simp [hwf]
      · simp [hmatch]

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
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
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

/-! Cake's top-level `evaluate_decls` boundary: once declaration evaluation
    has produced the function/global state and the selected call has returned
    one value, the program evaluator preserves that result exactly when the
    entry return shape accepts the value.  The declaration state, globals,
    call result, and shape check remain explicit for the correctness bridge. -/
theorem evalPanValueProgram_of_declarations_and_returned_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (shape : Shape) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (value : PanValue α)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.returned locals globals memory [value]))
    (hentry : lookupInfo entry state.returnShapes = some shape)
    (hshape : panShapeMatches (panValueShape state.structs value) shape = true) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.returned locals globals memory [value]) := by
  simp [evalPanValueProgram, hdeclarations, hcall, hentry, hshape]

/-! The raised-result counterpart keeps arbitrary exception payloads visible at
    the same top-level declaration/call boundary.  Unlike a returned value,
    a raised call does not require an entry return-shape premise. -/
theorem evalPanValueProgram_of_declarations_and_raised_call
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) := by
  simp [evalPanValueProgram, hdeclarations, hcall]

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
  simp [evalPanValueDeclarations, collectPanValueStructs,
    evalPanValueDeclarationsWithStructs]

/-! Cake's `evaluate_decls_functions_wf` (`pan_globalsProofScript.sml:2367`):
    a successful declaration evaluation only installs function declarations
    whose parameter and return shapes are well formed in the struct context.
    Flapjack checks well-formedness before installing a function, so the
    invariant is immediate by induction on the declaration list. -/
theorem evalPanValueDeclarationsWithStructs_functions_wf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state')
    {declaration : FunDecl α} (hmem : (.function declaration : Decl α) ∈ declarations) :
    declaration.params.all (fun parameter => isWfShape structs parameter.2) = true ∧
      isWfShape structs declaration.returnShape = true := by
  induction declarations generalizing state state' with
  | nil => simp at hmem
  | cons head tail ih =>
      cases head with
      | name name fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          simp at hmem
          exact ih state state' heval hmem
      | decl shape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at heval
                simp at hmem
                exact ih _ _ heval hmem
              · simp [hval, hmatch] at heval
      | function function =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (function.params.all
              (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape) = true
          · simp [hwf] at heval
            simp only [List.mem_cons] at hmem
            rcases hmem with hhead | htail
            · cases hhead
              simpa only [Bool.and_eq_true] using hwf
            · exact ih _ _ heval htail
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp [hexists, hwf] at heval
              simp at hmem
              exact ih _ _ heval hmem
            · simp [hexists, hwf] at heval

/-- Cake's `evaluate_decls_functions_wf` stated for the struct-collecting entry
    point `evalPanValueDeclarations`: a function declaration in a successfully
    evaluated list has well-formed shapes in the context collected from that
    list. -/
theorem evalPanValueDeclarations_functions_wf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state')
    {declaration : FunDecl α} (hmem : (.function declaration : Decl α) ∈ declarations) :
    ∃ structs : StructContext,
      collectPanValueStructs declarations state.structs = some structs ∧
        declaration.params.all (fun parameter => isWfShape structs parameter.2) = true ∧
        isWfShape structs declaration.returnShape = true := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      obtain ⟨hparams, hreturn⟩ :=
        evalPanValueDeclarationsWithStructs_functions_wf structs
          { state with structs := structs } state' declarations memoryAccess heval hmem
      exact ⟨structs, rfl, hparams, hreturn⟩

/-! Cake's `evaluate_decls_exns_wf` (`panPropsScript.sml:1421`): a successful
    declaration evaluation can only install an exception declaration whose
    shape is well formed in the struct context.  This is the exception-side
    counterpart of `evalPanValueDeclarationsWithStructs_functions_wf`. -/
theorem evalPanValueDeclarationsWithStructs_exceptions_wf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state')
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations) :
    isWfShape structs shape = true := by
  induction declarations generalizing state state' with
  | nil => simp at hmem
  | cons head tail ih =>
      cases head with
      | name name fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          simp at hmem
          exact ih state state' heval hmem
      | decl declShape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) declShape = true
              · simp [hval, hmatch] at heval
                simp at hmem
                exact ih _ _ heval hmem
              · simp [hval, hmatch] at heval
      | function function =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (function.params.all
              (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape) = true
          · simp [hwf] at heval
            simp at hmem
            exact ih _ _ heval hmem
          · simp [hwf] at heval
      | exnDecl headException headShape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo headException state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs headShape = true
            · simp [hexists, hwf] at heval
              simp only [List.mem_cons] at hmem
              rcases hmem with hhead | htail
              · cases hhead
                exact hwf
              · exact ih _ _ heval htail
            · simp [hexists, hwf] at heval

/-! The same exception-shape invariant at the struct-collecting entry point,
    where the successful declaration list determines the context used for
    `isWfShape`. -/
theorem evalPanValueDeclarations_exceptions_wf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state')
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations) :
    ∃ structs : StructContext,
      collectPanValueStructs declarations state.structs = some structs ∧
        isWfShape structs shape = true := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      have hwf := evalPanValueDeclarationsWithStructs_exceptions_wf structs
        { state with structs := structs } state' declarations memoryAccess heval hmem
      exact ⟨structs, rfl, hwf⟩

end Flapjack
