import Flapjack.CrepeDecCallRelation

/-!
Independent-fuel source/Crep composition for declaration calls.

The source and target evaluators are not required to consume the same fuel.
This is the form needed by PanValueCrepProgramCorrect, whose induction
quantifies over the two fuel parameters separately.
-/

namespace Flapjack

theorem compile_full_pan_value_decCall_relation_independent_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state callState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (hsourceCall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        [sourceValue]))
    (hsourceShape : panShapeMatches
      (panValueShape structs sourceValue) shape = true)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (updatePanValueMap sourceLocals name sourceValue)
      sourceCalleeGlobals sourceCalleeMemory body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { state with
          locals := initializeCrepLocals state.locals
            (allocatedNames context shape) }
      (some (allocatedNames context shape, none)) function compiledArguments =
      some (.normal callState))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) callState
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult)
    (hrel : panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult)) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.decCall name shape function arguments body)
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (restorePanValueControlLocal name (sourceLocals name) sourceResult) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (targetFuel + (allocatedNames context shape).length + 2) state
      (compileProg context (.decCall name shape function arguments body)) =
      some (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) ∧
    panValueCrepControlRel structs context exceptionRel
      (restorePanValueControlLocal name (sourceLocals name) sourceResult)
      (restoreCrepResultList state.locals
        (allocatedNames context shape) crepResult) := by
  have hsourceResult := evalPanValueProg_decCall_compose
    primitive sourceHandler structs sourceFunctions
    sourceLocals sourceGlobals sourceMemory
    baseAddress topAddress bytesInWord sourceFuel contracts
    memoryAccess memoryHandler name shape function arguments body
    sourceCalleeGlobals sourceCalleeMemory sourceValue sourceResult
    hsourceCall hsourceShape hsourceBody
  have hcrepResult := compile_full_pan_value_decCall_compose
    context functions crepPrimitive ffi sharedMem
    baseAddress topAddress targetFuel state callState crepResult
    name shape function arguments body compiledArguments
    hcompileArgs hcrepCall hcrepBody
  exact ⟨hsourceResult, hcrepResult, hrel⟩

end Flapjack
