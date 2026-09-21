import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.CrepeProgramSharedMemoryLoadStateCorrectness

namespace Flapjack

theorem panValuePcCompileCorrect_compact_shMemLoad_source_word
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (size : OpSize) (name : VarName) (address : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue oldValue : α)
      (slot : Nat),
      sharedMem (loadMemOp size) slot addressValue state = some targetState →
      sourceLocals name = some (.word oldValue) →
      panValueCrepStateRel structs context
        (updatePanValueMap sourceLocals name (.word valueValue)) sourceGlobals
        sourceMemory targetState)
    (hcontrolSafe : PanValueCrepProgramStateControlSafe
      (.shMemLoad size .local name address.toExp))
    (hraise : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.shMemLoad size .local name address.toExp) := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs _hlocalisedCode _hlocalised
    _hcode _hexcp hstate _hnonerror hsourceEval htargetEval _hpostCode _hpostExcp
  obtain ⟨sourceResult, hsource, hsourceResult⟩ :=
    panValuePcCompactSourceEvaluator_adapter primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      (.shMemLoad size .local name address.toExp)
      context structs sourceInput targetInput sourceExecution hsourceStructs hsourceEval
  obtain ⟨crepResult, hcrep, hcrepResult⟩ :=
    crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      (.shMemLoad size .local name address.toExp)
      context structs sourceInput targetInput targetExecution htargetStructs htargetEval
  have hcontrol := panValueCrepProgramStateCorrect_shMemLoad_source_word
    size name address hbytesInWord hlookup hsharedRel
    context structs sourceFunctions functions sourceInput.locals sourceInput.globals
    sourceInput.memory targetInput.state primitive sourceHandler crepPrimitive ffi
    sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hstate hsource hcrep
  have hsafe := hcontrolSafe context structs sourceFunctions functions
    sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
    hstate hsource hcrep
  have hresult := panValuePcResultRel_of_control
    structs context exceptionRel exceptionCode globalsLookup
    (hraise context structs exceptionRel)
    sourceResult crepResult targetExecution.result hcontrol hsafe hcrepResult
  rw [hsourceResult]
  exact hresult

end Flapjack
