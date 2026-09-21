import Flapjack.PanToCrepCorrectnessBridge

/-!
# Compact `pc_compile_correct` assembly for calls

The detailed call-state relation and handler-control proofs live in the Crep
call modules.  This file supplies the missing constructor-level assembly,
mirroring the `Call` branch of CakeML's `pc_compile_correct`: the caller must
provide both state simulation and handler-safe control evidence, and the
generic raised-state boundary supplies the result relation.
-/

namespace Flapjack

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_call_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (name : FunName) (arguments : List (Exp α))
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
    (hprogram : PanValueCrepProgramStateCorrect
      (.call info name arguments))
    (hprogramSafe : PanValueCrepProgramStateControlSafe
      (.call info name arguments))
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
      (.call info name arguments) := by
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.call info name arguments) codeRel excpRel exceptionCode globalsLookup
    sourceFunctions functions primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel hprogram hprogramSafe
    hpost hcode hlookup hsize

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_decCall_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
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
    (hprogram : PanValueCrepProgramStateCorrect
      (.decCall name shape function arguments body))
    (hprogramSafe : PanValueCrepProgramStateControlSafe
      (.decCall name shape function arguments body))
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
      (.decCall name shape function arguments body) := by
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.decCall name shape function arguments body) codeRel excpRel exceptionCode
    globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
    ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
    hprogram hprogramSafe hpost hcode hlookup hsize

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_extCall_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName) (configuration configurationLength : Exp α)
    (array arrayLength : Exp α)
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
    (hprogram : PanValueCrepProgramStateCorrect
      (.extCall function configuration configurationLength array arrayLength))
    (hprogramSafe : PanValueCrepProgramStateControlSafe
      (.extCall function configuration configurationLength array arrayLength))
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
      (.extCall function configuration configurationLength array arrayLength) := by
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.extCall function configuration configurationLength array arrayLength)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hpost hcode hlookup
    hsize

end Flapjack
