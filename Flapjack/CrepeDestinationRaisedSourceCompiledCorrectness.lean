import Flapjack.SourceCompiledDestinationRaisedCallPair
import Flapjack.CrepeCallRaisedCorrectness

/-!
Correctness composition for a raised call whose Crep metadata carries
destinations.  Raised results bypass destination assignment, but the
destination-aware call is the form generated for declaration calls.
-/

namespace Flapjack

theorem compile_full_pan_value_destination_call_raised_of_source_compiled_call
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (context functionContext : CompileContext α) (structs : StructContext)
    (declarations : List (Decl α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (caller : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (function : FunName) (arguments : List (Exp α))
    (compiledArguments : List (CrepExp α)) (destinations : List Nat)
    (_sourceCalleeLocals _sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (target : CrepState α) (crepException : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hsourceFunctions : sourceFunctions = sourceFunctionEntries declarations)
    (hfunctions : functions = compileToCrepe functionContext declarations)
    (hcontext : functionContext.vars = [])
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = caller.memory)
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
      evalPanValueExps structs (fun _ => none) sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments = some sourceValues →
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress compiledArguments = some targetValues →
      targetValues = sourceValues.flatMap panValueFlatWords)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      (fun _ => none) sourceGlobals sourceMemory none function arguments =
      some (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
      (some (destinations, none)) function compiledArguments =
      some (.raised target crepException))
    (hcalleeCorrect : ∀ declaration : FunDecl α,
      PanValueCrepProgramCorrect declaration.body) :
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (.raised target crepException) := by
  obtain ⟨sourceArgumentValues, sourceParameters, sourceBody,
      sourceCalleeLocals, sourceBodyLocals, declaration, compiledValues,
      targetParameters, targetBody, targetCalleeLocals, targetCallee,
      hsourceArguments, hlookupSource, hbind, hsourceBody, hnameDeclaration,
      hparams, hbodyDeclaration, hcompiledValues, hlookupCompiled,
      htargetParameters, htargetBody, hcompileBody, hassign, hcrepBody,
      htarget, hstate⟩ := sourceCompiledDestinationRaisedCallPair
    functionContext structs declarations sourceFunctions functions
    (fun _ => none) sourceGlobals sourceMemory caller caller.memory
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel none none none
    function arguments compiledArguments destinations sourceCalleeGlobals
    sourceCalleeMemory sourceException sourceValue target crepException
    hsourceFunctions hfunctions hcontext hglobals hmemory hshape hparameterLength hnames
    (fun sourceValues targetValues => hargumentValues sourceValues targetValues)
    hsourceCall hcrepCall
  let calleeContext : CompileContext α :=
    { functionContext with
        functions := functionInfos declarations
        vars := (compileParamVars declaration.params 0).1
        maxVar := (compileParamVars declaration.params 0).2.2 }
  have hstate' : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := caller.memory } := by
    simpa [calleeContext, panValueCrepStateRel, panValueCrepLocalsRel] using hstate
  have hbodyCorrect : PanValueCrepProgramCorrect sourceBody := by
    have h := hcalleeCorrect declaration
    rw [hbodyDeclaration] at h
    exact h
  have hcompileBody' : compileProg calleeContext sourceBody = targetBody := by
    rw [← hbodyDeclaration]
    simpa [calleeContext] using hcompileBody
  have hbodyRel := hbodyCorrect calleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := caller.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
      sourceException sourceValue)
    (.raised targetCallee crepException) hstate' hsourceBody (by
      rw [hcompileBody']
      exact hcrepBody)
  exact compile_full_pan_value_call_raised_of_body_correct
    context calleeContext structs sourceFunctions functions sourceGlobals caller
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel function compiledArguments
    sourceCalleeLocals sourceBodyLocals sourceCalleeGlobals sourceMemory sourceCalleeMemory
    sourceException sourceValue compiledValues targetCalleeLocals targetCallee target
    crepException (some destinations) targetParameters sourceBody targetBody
    exceptionRel hbodyCorrect hstate'
    hsourceBody hcompileBody' hcrepBody hcompiledValues hlookupCompiled hassign hcrepCall

end Flapjack
