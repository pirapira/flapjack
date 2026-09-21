import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.CrepeProgramDeclarationContract

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_dec
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (hbody : ∀ (primitive : PanPrimitiveHandler α)
      (handler : PanValueFfiHandler α) (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α),
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord body) :
    PanValueCrepProgramStateControlSafe (.dec name shape value body) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hnot := PanValueProgNotBrokeContinued_dec primitive sourceHandler structs
    sourceFunctions baseAddress topAddress bytesInWord name shape value body
    (hbody primitive sourceHandler structs sourceFunctions baseAddress topAddress
      bytesInWord)
  exact panValuePcControlLabelSafe_of_not_broke_continued sourceResult crepResult
    (hnot sourceFuel sourceLocals sourceGlobals sourceMemory sourceResult hsource)

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_dec_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodyNotBroke : ∀ (primitive : PanPrimitiveHandler α)
      (handler : PanValueFfiHandler α) (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α),
      PanValueProgNotBrokeContinued primitive handler structs functions
        baseAddress topAddress bytesInWord body)
    (hname : ∀ (context : CompileContext α),
      lookupInfo name context.vars = none)
    (hbounded : ∀ (context : CompileContext α) oldName oldShape oldSlots,
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ oldSlots, slot ≤ context.maxVar)
    (hcompile : ∀ (context : CompileContext α),
      ∃ compiledValues,
        compileExp context value = (compiledValues, shape) ∧
        (allocatedNames context shape).length = compiledValues.length)
    (hshape : ∀ (_context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α),
      ∃ sourceValue,
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord value = some sourceValue ∧
        panShapeMatches (panValueShape structs sourceValue) shape = true)
    (hvalue : PanValueCrepExpressionStateCorrect value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hpost : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState)
    (hcode : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.dec name shape value body) := by
  have hprogram := panValueCrepProgramStateCorrect_dec_of_expression_contract
    name shape value body hbody hname hbounded hcompile hshape hvalue
  have hprogramSafe := panValueCrepProgramStateControlSafe_dec name shape value body
    hbodyNotBroke
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.dec name shape value body) codeRel excpRel exceptionCode globalsLookup
    sourceFunctions functions primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel hprogram hprogramSafe
    hpost hcode hlookup hsize

end Flapjack
