import Flapjack.CrepeRaisedCallInversion
import Flapjack.CrepeProgramDeclarationCallCorrectness

/-!
Normal-return declaration-call composition.

This is the first end-to-end declaration-call correctness boundary: a
recursively correct source callee is related to its compiled body, its
flattened result is assigned to fresh destinations, and the continuation is
then related by its recursive correctness theorem.
-/

namespace Flapjack

theorem compile_full_pan_value_decCall_returned_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceCallFuel targetCallFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (name : VarName) (shape : Shape) (function : FunName)
    (calleeContext : CompileContext α)
    (arguments : List (Exp α)) (body : Prog α)
    (sourceCalleeBody : Prog α) (targetCalleeBody : CrepProg α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceBodyLocals : VarName → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (argumentValues targetValues : List α)
    (parameters : List Nat) (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (targetCallerLocals : Nat → Option α)
    (crepResult : CrepControlResult α)
    (hcontinuation : PanValueCrepProgramCorrect body)
    (hcalleeCorrect : PanValueCrepProgramCorrect sourceCalleeBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := state.memory })
    (hcompileCalleeBody : compileProg calleeContext sourceCalleeBody = targetCalleeBody)
    (hsourceCalleeBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceCallFuel
      sourceCalleeLocals sourceGlobals sourceMemory sourceCalleeBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        (sourceValue :: [])))
    (hcrepCalleeBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetCallFuel
      { locals := targetCalleeLocals, memory := state.memory } targetCalleeBody =
      some (.returned targetCallee targetValues))
    (hvalues : evalCrepFullExps
      (initializeCrepLocals state.locals (allocatedNames context shape)) state.memory
      baseAddress topAddress compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions = some (parameters, targetCalleeBody))
    (hassign : assignCrepValues (fun _ => none) parameters argumentValues =
      some targetCalleeLocals)
    (hdestinations : assignCrepValues
      (initializeCrepLocals state.locals (allocatedNames context shape))
      (allocatedNames context shape) targetValues = some targetCallerLocals)
    (hcalleeValues : targetValues = panValueFlatWords sourceValue)
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
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetCallFuel + 2)
      { locals := targetCallerLocals, memory := targetCallee.memory }
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult)
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
  have hbridge := evalCrepFullCall_returned_state_extension_of_body_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    { state with
        locals := initializeCrepLocals state.locals (allocatedNames context shape) }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceCallFuel targetCallFuel exceptionRel
    name shape function calleeContext sourceCalleeBody targetCalleeBody compiledArguments
    sourceCalleeLocals sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals
    [sourceValue] argumentValues targetValues parameters targetCalleeLocals
    targetCallee targetCallerLocals sourceValue hcalleeCorrect hcompileCalleeBody
    hrelCallee hsourceCalleeBody hcrepCalleeBody hvalues hlookup hassign hdestinations
    hcalleeValues hsourceShape hdistinct hfresh hinitRel
  have hresult := panValueCrepDecCall_of_body_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    state { locals := targetCallerLocals, memory := targetCallee.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord (sourceCallFuel + 1) (targetCallFuel + 1)
    name shape function arguments body compiledArguments sourceCalleeGlobals
    sourceCalleeMemory sourceValue sourceResult crepResult exceptionRel
    hcontinuation hbridge.2 hcompileArgs hsourceCall hsourceShape hsourceBody hbridge.1 hcrepBody
    hname hfresh
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

theorem compile_full_pan_value_decCall_state_returned_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceCallFuel targetCallFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (name : VarName) (shape : Shape) (function : FunName)
    (calleeContext : CompileContext α)
    (arguments : List (Exp α)) (body : Prog α)
    (sourceCalleeBody : Prog α) (targetCalleeBody : CrepProg α)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceBodyLocals : VarName → Option (PanValue α))
    (sourceValue : PanValue α) (sourceResult : PanValueControlResult α)
    (argumentValues targetValues : List α)
    (parameters : List Nat) (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (targetCallerLocals : Nat → Option α)
    (crepResult : CrepControlResult α)
    (hcontinuation : PanValueCrepProgramStateCorrect body)
    (hcalleeCorrect : PanValueCrepProgramStateCorrect sourceCalleeBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := state.memory,
        globals := state.globals })
    (hcompileCalleeBody : compileProg calleeContext sourceCalleeBody = targetCalleeBody)
    (hsourceCalleeBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceCallFuel
      sourceCalleeLocals sourceGlobals sourceMemory sourceCalleeBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        (sourceValue :: [])))
    (hcrepCalleeBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetCallFuel
      { locals := targetCalleeLocals, memory := state.memory,
        globals := state.globals } targetCalleeBody =
      some (.returned targetCallee targetValues))
    (hvalues : evalCrepFullExpsState
      { state with
          locals := initializeCrepLocals state.locals (allocatedNames context shape) }
      baseAddress topAddress compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions = some (parameters, targetCalleeBody))
    (hassign : assignCrepValues (fun _ => none) parameters argumentValues =
      some targetCalleeLocals)
    (hdestinations : assignCrepValues
      (initializeCrepLocals state.locals (allocatedNames context shape))
      (allocatedNames context shape) targetValues = some targetCallerLocals)
    (hcalleeValues : targetValues = panValueFlatWords sourceValue)
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
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetCallFuel + 2)
      { locals := targetCallerLocals, memory := targetCallee.memory,
        globals := targetCallee.globals }
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body) = some crepResult)
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
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
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
  have hbridge := evalCrepFullCallState_returned_state_extension_of_body_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    { state with
        locals := initializeCrepLocals state.locals (allocatedNames context shape) }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceCallFuel targetCallFuel exceptionRel
    name shape function calleeContext sourceCalleeBody targetCalleeBody compiledArguments
    sourceCalleeLocals sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals
    [sourceValue] argumentValues targetValues parameters targetCalleeLocals
    targetCallee targetCallerLocals sourceValue hcalleeCorrect hcompileCalleeBody
    hrelCallee hsourceCalleeBody hcrepCalleeBody hvalues hlookup hassign hdestinations
    hcalleeValues hsourceShape hdistinct hfresh hinitRel
  have hresult := panValueCrepDecCall_state_of_body_correct
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    state
    { locals := targetCallerLocals, memory := targetCallee.memory,
      globals := targetCallee.globals }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord (sourceCallFuel + 1) (targetCallFuel + 1)
    name shape function arguments body compiledArguments sourceCalleeGlobals
    sourceCalleeMemory sourceValue sourceResult crepResult exceptionRel
    hcontinuation hbridge.2 hcompileArgs hsourceCall hsourceShape hsourceBody
    hbridge.1 hcrepBody hname hfresh
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

end Flapjack
