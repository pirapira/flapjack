import Flapjack.CrepeCallNormalInversion
import Flapjack.SourceCompiledCalleeCallState

/-!
Source/compiled witness pairing for a destination-aware normal call.

The target inversion has two result branches.  This theorem derives the
source callee state relation in either branch and leaves branch selection to
the recursive correctness theorem.
-/

namespace Flapjack

theorem sourceCompiledDestinationCallPair
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
    (caller : CrepState α)
    (crepMemory : α → Option α)
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α))
    (destinations : List Nat) (target : CrepState α)
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α)
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
    (hargumentValues : ∀ (sourceValues : List (PanValue α))
      (targetValues : List α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some sourceValues →
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress compiledArguments = some targetValues →
      targetValues = sourceValues.flatMap panValueFlatWords)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hcall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
      (some (destinations, none)) function compiledArguments =
      some (.normal target)) :
    ∃ (sourceArgumentValues : List (PanValue α))
        (sourceParameters : List VarName) (sourceBody : Prog α)
        (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
        (declaration : FunDecl α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some sourceArgumentValues ∧
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (sourceParameters, sourceBody) ∧
      bindPanValueParameters sourceParameters sourceArgumentValues =
        some sourceCalleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel
        sourceCalleeLocals sourceGlobals sourceMemory sourceBody
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
          some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
            [sourceValue]) ∧
      declaration.name = function ∧
      declaration.params.map Prod.fst = sourceParameters ∧
      declaration.body = sourceBody ∧
      ((∃ (targetArgumentValues : List α) (targetParameters : List Nat)
          (targetBody : CrepProg α) (targetCalleeLocals : Nat → Option α)
          (targetCallee : CrepState α),
        evalCrepFullExps caller.locals caller.memory
          baseAddress topAddress compiledArguments = some targetArgumentValues ∧
        lookupCompiledFunction function functions =
          some (targetParameters, targetBody) ∧
        targetParameters =
          (compileFunDecl
            { functionContext with functions := functionInfos declarations } declaration).params ∧
        targetBody =
          (compileFunDecl
            { functionContext with functions := functionInfos declarations } declaration).body ∧
        compileProg
            { functionContext with
                functions := functionInfos declarations
                vars := (compileParamVars declaration.params 0).1
                maxVar := (compileParamVars declaration.params 0).2.2 }
            declaration.body = targetBody ∧
        assignCrepValues (fun _ => none) targetParameters targetArgumentValues =
          some targetCalleeLocals ∧
        evalCrepFullProg functions crepPrimitive ffi sharedMem
          baseAddress topAddress targetFuel
          { locals := targetCalleeLocals, memory := caller.memory } targetBody =
            some (.normal targetCallee) ∧
        target = { caller with memory := targetCallee.memory } ∧
        panValueCrepStateRel structs
          { functionContext with
              functions := functionInfos declarations
              vars := (compileParamVars declaration.params 0).1 }
          sourceCalleeLocals sourceGlobals sourceMemory
          { locals := targetCalleeLocals, memory := crepMemory }) ∨
      (∃ (targetArgumentValues : List α) (targetParameters : List Nat)
          (targetBody : CrepProg α) (targetCalleeLocals : Nat → Option α)
          (targetCallee : CrepState α) (targetCalleeValues : List α)
          (targetCallerLocals : Nat → Option α),
        evalCrepFullExps caller.locals caller.memory
          baseAddress topAddress compiledArguments = some targetArgumentValues ∧
        lookupCompiledFunction function functions =
          some (targetParameters, targetBody) ∧
        targetParameters =
          (compileFunDecl
            { functionContext with functions := functionInfos declarations } declaration).params ∧
        targetBody =
          (compileFunDecl
            { functionContext with functions := functionInfos declarations } declaration).body ∧
        compileProg
            { functionContext with
                functions := functionInfos declarations
                vars := (compileParamVars declaration.params 0).1
                maxVar := (compileParamVars declaration.params 0).2.2 }
            declaration.body = targetBody ∧
        assignCrepValues (fun _ => none) targetParameters targetArgumentValues =
          some targetCalleeLocals ∧
        evalCrepFullProg functions crepPrimitive ffi sharedMem
          baseAddress topAddress targetFuel
          { locals := targetCalleeLocals, memory := caller.memory } targetBody =
            some (.returned targetCallee targetCalleeValues) ∧
        assignCrepValues caller.locals destinations targetCalleeValues =
          some targetCallerLocals ∧
        target = { locals := targetCallerLocals, memory := targetCallee.memory } ∧
        panValueCrepStateRel structs
          { functionContext with
              functions := functionInfos declarations
              vars := (compileParamVars declaration.params 0).1 }
          sourceCalleeLocals sourceGlobals sourceMemory
          { locals := targetCalleeLocals, memory := crepMemory })) := by
  obtain hnormal | hreturned := evalCrepFullCall_normal_inversion
    functions crepPrimitive ffi sharedMem baseAddress topAddress targetFuel caller
    destinations function compiledArguments target hcall
  · obtain ⟨targetArgumentValues, targetParameters, targetBody,
        targetCalleeLocals, targetCallee, htargetValues, hlookupCompiled,
        hassign, hcrepBody, htarget⟩ := hnormal
    obtain ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
        sourceBodyLocals, declaration, hsourceArguments, hlookupSource, hbind,
        hsourceBody, hname, hparams, hbody, htargetParameters, htargetBody,
        hcompileBody, hstate⟩ :=
      sourceCompiledCalleeState_of_returned_call functionContext structs declarations
        sourceFunctions functions sourceLocals sourceGlobals sourceMemory crepMemory
        primitive handler baseAddress topAddress bytesInWord sourceFuel contracts
        memoryAccess memoryHandler function arguments sourceCalleeGlobals sourceCalleeMemory
        sourceValue targetParameters targetBody targetArgumentValues targetCalleeLocals
        hsourceFunctions hfunctions hcontext hglobals hmemory hshape hparameterLength hnames
        hsourceCall hlookupCompiled
        (fun sourceValues hsourceArguments =>
          hargumentValues sourceValues targetArgumentValues hsourceArguments htargetValues)
        hassign
    exact ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
      sourceBodyLocals, declaration, hsourceArguments, hlookupSource, hbind, hsourceBody,
      hname, hparams, hbody,
      Or.inl ⟨targetArgumentValues, targetParameters, targetBody,
        targetCalleeLocals, targetCallee, htargetValues, hlookupCompiled,
        htargetParameters, htargetBody, hcompileBody, hassign, hcrepBody,
        htarget, hstate⟩⟩
  · obtain ⟨targetArgumentValues, targetParameters, targetBody,
        targetCalleeLocals, targetCallee, targetCalleeValues, targetCallerLocals,
        htargetValues, hlookupCompiled, hassign, hcrepBody, hdestinations, htarget⟩ :=
      hreturned
    obtain ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
        sourceBodyLocals, declaration, hsourceArguments, hlookupSource, hbind,
        hsourceBody, hname, hparams, hbody, htargetParameters, htargetBody,
        hcompileBody, hstate⟩ :=
      sourceCompiledCalleeState_of_returned_call functionContext structs declarations
        sourceFunctions functions sourceLocals sourceGlobals sourceMemory crepMemory
        primitive handler baseAddress topAddress bytesInWord sourceFuel contracts
        memoryAccess memoryHandler function arguments sourceCalleeGlobals sourceCalleeMemory
        sourceValue targetParameters targetBody targetArgumentValues targetCalleeLocals
        hsourceFunctions hfunctions hcontext hglobals hmemory hshape hparameterLength hnames
        hsourceCall hlookupCompiled
        (fun sourceValues hsourceArguments =>
          hargumentValues sourceValues targetArgumentValues hsourceArguments htargetValues)
        hassign
    exact ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
      sourceBodyLocals, declaration, hsourceArguments, hlookupSource, hbind, hsourceBody,
      hname, hparams, hbody,
      Or.inr ⟨targetArgumentValues, targetParameters, targetBody,
        targetCalleeLocals, targetCallee, targetCalleeValues, targetCallerLocals,
        htargetValues, hlookupCompiled, htargetParameters, htargetBody, hcompileBody,
        hassign, hcrepBody, hdestinations, htarget, hstate⟩⟩

end Flapjack
