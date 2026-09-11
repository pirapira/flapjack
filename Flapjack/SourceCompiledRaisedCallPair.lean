import Flapjack.CrepeCallRaisedInversion
import Flapjack.SourceCompiledCalleeEntry

/-!
Paired source/compiled inversion for an ordinary raised call.

This packages the source and Crep call inversions with the compiled callee
state theorem.  The result is the witness boundary used by the raised-call
correctness composition.
-/

namespace Flapjack

theorem sourceCompiledRaisedCallPair
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
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (target : CrepState α) (crepException : α)
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
        baseAddress topAddress bytesInWord arguments = some sourceValues →
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress compiledArguments = some targetValues →
      targetValues = sourceValues.flatMap panValueFlatWords)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments
      =
      some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller none function compiledArguments =
      some (.raised target crepException)) :
    ∃ (sourceArgumentValues : List (PanValue α))
        (sourceParameters : List VarName) (sourceBody : Prog α)
        (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
        (declaration : FunDecl α) (compiledValues : List α)
        (targetParameters : List Nat) (targetBody : CrepProg α)
        (targetCalleeLocals : Nat → Option α) (targetCallee : CrepState α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments = some sourceArgumentValues ∧
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (sourceParameters, sourceBody) ∧
      bindPanValueParameters sourceParameters sourceArgumentValues =
        some sourceCalleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel
        sourceCalleeLocals sourceGlobals sourceMemory sourceBody =
          some (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
            sourceException sourceValue) ∧
      declaration.name = function ∧
      declaration.params.map Prod.fst = sourceParameters ∧
      declaration.body = sourceBody ∧
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress compiledArguments = some compiledValues ∧
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
      assignCrepValues (fun _ => none) targetParameters compiledValues =
        some targetCalleeLocals ∧
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel
        { locals := targetCalleeLocals, memory := caller.memory } targetBody =
          some (.raised targetCallee crepException) ∧
      target = { caller with memory := targetCallee.memory } ∧
      panValueCrepStateRel structs
        { functionContext with
            functions := functionInfos declarations
            vars := (compileParamVars declaration.params 0).1 }
        sourceCalleeLocals sourceGlobals sourceMemory
        { locals := targetCalleeLocals, memory := crepMemory } := by
  obtain ⟨compiledValues, targetParameters, targetBody, targetCalleeLocals,
      targetCallee, hcompiledValues, hlookupCompiled, hassign, hcrepBody, htarget⟩ :=
    evalCrepFullCall_none_raised_inversion functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel caller function compiledArguments crepException
      target hcrepCall
  obtain ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
      sourceBodyLocals, hsourceArguments, hlookupSource, _, hbind, hsourceBody, _, _⟩ :=
    evalPanValueCall_raised_inversion primitive handler structs sourceFunctions
      sourceLocals sourceGlobals sourceMemory baseAddress topAddress bytesInWord sourceFuel
      function arguments sourceCalleeGlobals sourceCalleeMemory sourceException sourceValue
      hsourceCall
  have hlookupSourceDecl : lookupPanFunction function
      (sourceFunctionEntries declarations) = some (sourceParameters, sourceBody) := by
    simpa [hsourceFunctions] using hlookupSource
  obtain ⟨declaration, hname, hparams, hbody, htargetParams, htargetBody,
      hcompileBody, hstate⟩ := sourceCompiledCalleeState_of_lookup
    structs functionContext declarations functions function sourceParameters sourceBody
    sourceGlobals sourceMemory crepMemory sourceArgumentValues targetParameters targetBody
    sourceCalleeLocals targetCalleeLocals hlookupSourceDecl hfunctions
    (by
      have hbindExpanded := hbind
      simp [bindPanValueParameters] at hbindExpanded
      exact hbindExpanded.1)
    hglobals hmemory hcontext (hnames sourceParameters sourceBody hlookupSourceDecl)
    (fun parameters returnShape => hshape parameters returnShape sourceArgumentValues)
    (fun parameters returnShape =>
      hparameterLength parameters returnShape sourceArgumentValues)
    hlookupCompiled hbind (by
      have htargetValues := hargumentValues sourceArgumentValues compiledValues
        hsourceArguments hcompiledValues
      rw [htargetValues] at hassign
      exact hassign)
  exact ⟨sourceArgumentValues, sourceParameters, sourceBody, sourceCalleeLocals,
    sourceBodyLocals, declaration, compiledValues, targetParameters, targetBody,
    targetCalleeLocals, targetCallee, hsourceArguments, hlookupSourceDecl, hbind,
    hsourceBody, hname, hparams, hbody, hcompiledValues, hlookupCompiled,
    htargetParams, htargetBody, hcompileBody, hassign, hcrepBody, htarget, hstate⟩

end Flapjack
