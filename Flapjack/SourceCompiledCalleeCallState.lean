import Flapjack.PanValueCallReturnedInversion
import Flapjack.SourceCompiledCalleeEntry

/-!
Returned-call inversion at the source/compiled callee-state boundary.

The source call evaluator exposes structured argument values and a name-based
callee environment.  The compiled call evaluator exposes flattened argument
words and slot-based locals.  This adapter combines source call inversion with
the compiler lookup/state theorem so declaration-call correctness can consume
one witness package.
-/

namespace Flapjack

theorem sourceCompiledCalleeState_of_returned_call
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (functionContext : CompileContext α) (structs : StructContext)
    (declarations : List (Decl α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (baseAddress topAddress bytesInWord : α)
    (callFuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (function : FunName) (arguments : List (Exp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α)
    (targetParameters : List Nat) (targetBody : CrepProg α)
    (compiledArgumentValues : List α)
    (targetCalleeLocals : Nat → Option α)
    (hsourceFunctions : sourceFunctions = sourceFunctionEntries declarations)
    (hfunctions : functions = compileToCrepe functionContext declarations)
    (hcontext : functionContext.vars = [])
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = crepMemory)
    (hshape : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape)
      (values : List (PanValue α)),
      lookupInfo function (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape)
      (values : List (PanValue α)),
      lookupInfo function (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        parameter.slots.length = parameter.values.length)
    (hnames : ∀ (parameters : List VarName) (body : Prog α),
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (parameters, body) → parameters.Nodup)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs sourceFunctions
      baseAddress topAddress bytesInWord (callFuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hlookupCompiled : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hargumentValues : ∀ (values : List (PanValue α)),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some values →
      compiledArgumentValues = values.flatMap panValueFlatWords)
    (hassign : assignCrepValues (fun _ => none) targetParameters
      compiledArgumentValues = some targetCalleeLocals) :
    ∃ (argumentValues : List (PanValue α)) (parameters : List VarName)
      (body : Prog α) (calleeLocals bodyLocals : VarName → Option (PanValue α))
      (declaration : FunDecl α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some argumentValues ∧
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (parameters, body) ∧
      bindPanValueParameters parameters argumentValues = some calleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs sourceFunctions
        baseAddress topAddress bytesInWord callFuel
        calleeLocals sourceGlobals sourceMemory body
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
          some (.returned bodyLocals sourceCalleeGlobals sourceCalleeMemory [sourceValue]) ∧
      declaration.name = function ∧
      declaration.params.map Prod.fst = parameters ∧
      declaration.body = body ∧
      panValueCrepStateRel structs
        { functionContext with
            functions := functionInfos declarations
            vars := (compileParamVars declaration.params 0).1 }
        calleeLocals sourceGlobals sourceMemory
        { locals := targetCalleeLocals, memory := crepMemory } := by
  obtain ⟨argumentValues, parameters, body, calleeLocals, bodyLocals,
      harguments, hlookup, _, hbind, hbody, _, _⟩ :=
    evalPanValueCall_returned_inversion primitive handler structs sourceFunctions
      sourceLocals sourceGlobals sourceMemory baseAddress topAddress bytesInWord callFuel
      contracts memoryAccess memoryHandler function arguments
      sourceCalleeGlobals sourceCalleeMemory [sourceValue] hsourceCall
  have hbindExpanded := hbind
  simp [bindPanValueParameters] at hbindExpanded
  have hparametersLength : parameters.length = argumentValues.length :=
    hbindExpanded.1
  have hlookupDecl : lookupPanFunction function
      (sourceFunctionEntries declarations) = some (parameters, body) := by
    simpa [hsourceFunctions] using hlookup
  have hstate := sourceCompiledCalleeState_of_lookup
    structs functionContext declarations functions function parameters body
    sourceGlobals sourceMemory crepMemory argumentValues targetParameters targetBody
    calleeLocals targetCalleeLocals hlookupDecl hfunctions hparametersLength hglobals hmemory
    hcontext (hnames parameters body hlookupDecl)
    (fun parameters returnShape => hshape parameters returnShape argumentValues)
    (fun parameters returnShape => hparameterLength parameters returnShape argumentValues)
      hlookupCompiled hbind (by
      rw [hargumentValues argumentValues harguments] at hassign
      exact hassign)
  obtain ⟨declaration, hname, hparams, hbodyDeclaration,
      _, _, hrel⟩ := hstate
  exact ⟨argumentValues, parameters, body, calleeLocals, bodyLocals, declaration,
    harguments, hlookupDecl, hbind, hbody, hname, hparams, hbodyDeclaration, hrel⟩

theorem sourceCompiledCalleeState_of_returned_call_callee_memory
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (functionContext : CompileContext α) (structs : StructContext)
    (declarations : List (Decl α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceArgumentMemory sourceCalleeMemory : α → Option (PanValue α))
    (crepMemory : α → Option α)
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (baseAddress topAddress bytesInWord : α)
    (callFuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (function : FunName) (arguments : List (Exp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceValue : PanValue α)
    (targetParameters : List Nat) (targetBody : CrepProg α)
    (compiledArgumentValues : List α)
    (targetCalleeLocals : Nat → Option α)
    (hsourceFunctions : sourceFunctions = sourceFunctionEntries declarations)
    (hfunctions : functions = compileToCrepe functionContext declarations)
    (hcontext : functionContext.vars = [])
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceArgumentMemory = crepMemory)
    (hshape : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape)
      (values : List (PanValue α)),
      lookupInfo function (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        panShapeMatches (panValueShape structs parameter.value) parameter.shape = true)
    (hparameterLength : ∀ (parameters : List (VarName × Shape)) (returnShape : Shape)
      (values : List (PanValue α)),
      lookupInfo function (functionInfos declarations) =
        some (parameters, returnShape) →
      ∀ parameter ∈ compileCalleeParameterList parameters values 0,
        parameter.slots.length = parameter.values.length)
    (hnames : ∀ (parameters : List VarName) (body : Prog α),
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (parameters, body) → parameters.Nodup)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs sourceFunctions
      baseAddress topAddress bytesInWord (callFuel + 1)
      sourceLocals sourceGlobals sourceArgumentMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hlookupCompiled : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hargumentValues : ∀ (values : List (PanValue α)),
      evalPanValueExps structs sourceLocals sourceGlobals sourceArgumentMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some values →
      compiledArgumentValues = values.flatMap panValueFlatWords)
    (hassign : assignCrepValues (fun _ => none) targetParameters
      compiledArgumentValues = some targetCalleeLocals) :
    ∃ (argumentValues : List (PanValue α)) (parameters : List VarName)
      (body : Prog α) (calleeLocals bodyLocals : VarName → Option (PanValue α))
      (declaration : FunDecl α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceArgumentMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some argumentValues ∧
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (parameters, body) ∧
      bindPanValueParameters parameters argumentValues = some calleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs sourceFunctions
        baseAddress topAddress bytesInWord callFuel
        calleeLocals sourceGlobals sourceArgumentMemory body
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
          some (.returned bodyLocals sourceCalleeGlobals sourceCalleeMemory [sourceValue]) ∧
      declaration.name = function ∧
      declaration.params.map Prod.fst = parameters ∧
      declaration.body = body ∧
      panValueCrepStateRel structs
        { functionContext with
            functions := functionInfos declarations
            vars := (compileParamVars declaration.params 0).1 }
        calleeLocals sourceGlobals sourceArgumentMemory
        { locals := targetCalleeLocals, memory := crepMemory } := by
  obtain ⟨argumentValues, parameters, body, calleeLocals, bodyLocals,
      harguments, hlookup, _, hbind, hbody, _, _⟩ :=
    evalPanValueCall_returned_inversion primitive handler structs sourceFunctions
      sourceLocals sourceGlobals sourceArgumentMemory baseAddress topAddress bytesInWord
      callFuel contracts memoryAccess memoryHandler function arguments
      sourceCalleeGlobals sourceCalleeMemory [sourceValue] hsourceCall
  have hbindExpanded := hbind
  simp [bindPanValueParameters] at hbindExpanded
  have hparametersLength : parameters.length = argumentValues.length :=
    hbindExpanded.1
  have hlookupDecl : lookupPanFunction function
      (sourceFunctionEntries declarations) = some (parameters, body) := by
    simpa [hsourceFunctions] using hlookup
  have hstate := sourceCompiledCalleeState_of_lookup
    structs functionContext declarations functions function parameters body
    sourceGlobals sourceArgumentMemory crepMemory argumentValues targetParameters targetBody
    calleeLocals targetCalleeLocals hlookupDecl hfunctions hparametersLength hglobals hmemory
    hcontext (hnames parameters body hlookupDecl)
    (fun parameters returnShape => hshape parameters returnShape argumentValues)
    (fun parameters returnShape => hparameterLength parameters returnShape argumentValues)
    hlookupCompiled hbind (by
      simpa [hargumentValues argumentValues harguments] using hassign)
  obtain ⟨declaration, hname, hparams, hbodyDeclaration, _, _, hstate⟩ := hstate
  exact ⟨argumentValues, parameters, body, calleeLocals, bodyLocals, declaration,
    harguments, hlookupDecl, hbind, hbody, hname, hparams, hbodyDeclaration, hstate⟩

end Flapjack
