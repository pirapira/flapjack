import Flapjack.SourceCompiledDestinationReturnedCall
import Flapjack.CrepeDeclarationCallReturnedCorrectness

/-!
End-to-end declaration-call correctness from source/compiled call witnesses.

The source and target calls are inverted together, the normal target branch is
removed by recursive callee correctness, and the resulting returned branch is
passed to the declaration-call correctness boundary.
-/

namespace Flapjack

theorem compile_full_pan_value_decCall_returned_of_source_compiled_call
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (context functionContext : CompileContext α) (structs : StructContext)
    (declarations : List (Decl α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state callState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceCallFuel targetCallFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcontinuation : PanValueCrepProgramCorrect body)
    (hsourceFunctions : sourceFunctions = sourceFunctionEntries declarations)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceCallFuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hsourceShape : panShapeMatches
      (panValueShape structs sourceValue) shape = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceCallFuel + 1)
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body = some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetCallFuel + 1)
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal callState))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetCallFuel + 2)
      { locals := callState.locals, memory := callState.memory }
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult)
    (hcalleeCorrect : ∀ declaration : FunDecl α,
      PanValueCrepProgramCorrect declaration.body)
    (hfunctions : functions = compileToCrepe functionContext declarations)
    (hfunctionContext : functionContext.vars = [])
    (hglobals : sourceGlobals = (fun _ => none))
    (hmemory : panValueWordMemory sourceMemory = state.memory)
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
    (hnames : ∀ (parameters : List VarName) (calleeBody : Prog α),
      lookupPanFunction function (sourceFunctionEntries declarations) =
        some (parameters, calleeBody) → parameters.Nodup)
    (hargumentValues : ∀ (sourceValues : List (PanValue α))
      (targetValues : List α),
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments = some sourceValues →
      evalCrepFullExps
        (initializeCrepLocals state.locals (allocatedNames context shape)) state.memory
        baseAddress topAddress compiledArguments = some targetValues →
      targetValues = sourceValues.flatMap panValueFlatWords)
    (hdistinct : CrepDistinctNames (allocatedNames context shape))
    (hname : lookupInfo name context.vars = none)
    (hfresh : ∀ oldName oldShape oldSlots,
      oldName ≠ name →
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ temporary, temporary ∈ allocatedNames context shape →
        temporary ∉ oldSlots)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceCallFuel + 2)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name shape function arguments body) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (targetCallFuel + 1 + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  have hinitRel := panValueCrepStateRel_initialize structs context sourceLocals
    sourceGlobals sourceMemory state name (allocatedNames context shape) hrel hname hfresh
  have hpair := sourceCompiledDestinationCallPair_returned_of_body_correct
    functionContext structs declarations sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory
    { state with
        locals := initializeCrepLocals state.locals (allocatedNames context shape) }
    state.memory primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceCallFuel targetCallFuel none none none
    function arguments compiledArguments (allocatedNames context shape) callState
    sourceCalleeGlobals sourceCalleeMemory sourceValue hsourceFunctions hfunctions hfunctionContext
    hglobals hmemory hshape hparameterLength hnames hargumentValues hsourceCall hcrepCall
    rfl rfl rfl hcalleeCorrect rfl
  obtain ⟨sourceArgumentValues, sourceParameters, sourceCalleeBody,
      sourceCalleeLocals, sourceBodyLocals, declaration, targetArgumentValues,
      targetParameters, targetCalleeBody, targetCalleeLocals, targetCallee,
      targetCalleeValues, targetCallerLocals, hsourceArguments, hlookupSource,
      hbind, hsourceCallee, hnameDeclaration, hparams, hbodyDeclaration,
      htargetValues, hlookupCompiled, htargetParameters, htargetBody,
      hcompileCalleeBody, hassign, hcrepCalleeBody, hdestinations, htarget,
      hstate⟩ := hpair
  let hcalleeContext : CompileContext α :=
    { functionContext with
        functions := functionInfos declarations
        vars := (compileParamVars declaration.params 0).1
        maxVar := (compileParamVars declaration.params 0).2.2 }
  have hstate' : panValueCrepStateRel structs hcalleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := state.memory } := by
    simpa [hcalleeContext, panValueCrepStateRel, panValueCrepLocalsRel] using hstate
  have hbodyCorrect : PanValueCrepProgramCorrect sourceCalleeBody := by
    have h := hcalleeCorrect declaration
    rw [hbodyDeclaration] at h
    exact h
  have hcompileCalleeBody' : compileProg hcalleeContext sourceCalleeBody =
      targetCalleeBody := by
    rw [← hbodyDeclaration]
    simpa [hcalleeContext] using hcompileCalleeBody
  have hcrepCalleeBody' : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetCallFuel
      { locals := targetCalleeLocals, memory := state.memory }
      (compileProg hcalleeContext sourceCalleeBody) =
        some (.returned targetCallee targetCalleeValues) := by
    rw [hcompileCalleeBody']
    exact hcrepCalleeBody
  have hbodyRel := hbodyCorrect hcalleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := state.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceCallFuel targetCallFuel exceptionRel
    (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory [sourceValue])
    (.returned targetCallee targetCalleeValues) hstate' hsourceCallee hcrepCalleeBody'
  have hcalleeValues : targetCalleeValues = panValueFlatWords sourceValue := by
    simpa [panValueCrepControlRel, panValueCrepValuesRel] using hbodyRel.2
  have hcrepBody' := hcrepBody
  rw [htarget] at hcrepBody'
  exact compile_full_pan_value_decCall_returned_of_body_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceCallFuel targetCallFuel exceptionRel
    name shape function hcalleeContext arguments body sourceCalleeBody targetCalleeBody
    compiledArguments sourceCalleeLocals sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals
    sourceValue sourceResult targetArgumentValues targetCalleeValues targetParameters
    targetCalleeLocals
    targetCallee targetCallerLocals crepResult hcontinuation hbodyCorrect hstate'
    hcompileCalleeBody' hsourceCallee hcrepCalleeBody
    (by simpa using htargetValues) hlookupCompiled hassign hdestinations hcalleeValues
    hcompileArgs hsourceCall hsourceShape hsourceBody hcrepBody' hdistinct hname hfresh hrel

end Flapjack
