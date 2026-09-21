import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.CrepeWordProgramCases

/-!
# Pancake-shaped conditional correctness bridges

The evaluator proof is implemented for `SourceWordExp`, the checked scalar
condition representation used by the source-state contracts.  Pancake's
`pc_compile_correct` induction is stated over the original `Exp` syntax and
separately carries the `wordExp` invariant.  This wrapper exposes the same
correctness theorem at that AST boundary without changing any of the state,
control-safety, or raised-result premises.
-/

namespace Flapjack

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_ite_word_exp_of_state_evidence_context_code
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : Exp α) (hcondition : wordExp condition)
    (thenBranch elseBranch : Prog α)
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
    (hthenCorrect : PanValueCrepProgramStateCorrect thenBranch)
    (helseCorrect : PanValueCrepProgramStateCorrect elseBranch)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext α) (wordSize : α),
      context.bytesInWord = wordSize)
    (hlookupSource : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupExceptionControl : ∀ (context : CompileContext α)
      (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      lookupInfo sourceException context.exceptions = some targetException)
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
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.ite condition thenBranch elseBranch) := by
  have hconditionToExp :
      (sourceWordExpOf condition hcondition).toExp = condition :=
    sourceWordExpOf_toExp condition hcondition
  simpa [hconditionToExp] using
    (panValuePcCompileCorrect_compact_ite_source_word_of_state_evidence_context_code
      (condition := sourceWordExpOf condition hcondition)
      (thenBranch := thenBranch) (elseBranch := elseBranch)
      (codeRel := codeRel) (excpRel := excpRel)
      (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
      (sourceFunctions := sourceFunctions) (functions := functions)
      (primitive := primitive) (sourceHandler := sourceHandler)
      (crepPrimitive := crepPrimitive) (ffi := ffi) (sharedMem := sharedMem)
      (baseAddress := baseAddress) (topAddress := topAddress)
      (bytesInWord := bytesInWord) (sourceFuel := sourceFuel)
      (targetFuel := targetFuel) (hthenCorrect := hthenCorrect)
      (helseCorrect := helseCorrect) (hthenSafe := hthenSafe)
      (helseSafe := helseSafe) (hbytesInWord := hbytesInWord)
      (hlookupSource := hlookupSource)
      (hlookupExceptionControl := hlookupExceptionControl) (hpost := hpost)
      (hcode := hcode) (hlookup := hlookup) (hsize := hsize))

/-! The corresponding original-`Exp` adapter for `While`.  The loop-control
    safety premise is transported through the checked word-expression view;
    all evaluator and raised-payload premises stay explicit. -/
set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_while_word_exp_of_state_evidence_context_code
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (condition : Exp α) (hcondition : wordExp condition)
    (body : Prog α)
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
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition body))
    (hbytesInWord : ∀ (context : CompileContext α) (wordSize : α),
      context.bytesInWord = wordSize)
    (hlookupSource : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupExceptionControl : ∀ (context : CompileContext α)
      (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      lookupInfo sourceException context.exceptions = some targetException)
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
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup
      (.while condition body) := by
  have hconditionToExp :
      (sourceWordExpOf condition hcondition).toExp = condition :=
    sourceWordExpOf_toExp condition hcondition
  have hloopSafe' : PanValueCrepProgramLoopStateControlSafe
      (.while (sourceWordExpOf condition hcondition).toExp body) := by
    simpa [hconditionToExp] using hloopSafe
  simpa [hconditionToExp] using
    (panValuePcCompileCorrect_compact_while_source_word_of_state_evidence_context_code
      (condition := sourceWordExpOf condition hcondition)
      (body := body) (codeRel := codeRel) (excpRel := excpRel)
      (exceptionCode := exceptionCode) (globalsLookup := globalsLookup)
      (sourceFunctions := sourceFunctions) (functions := functions)
      (primitive := primitive) (sourceHandler := sourceHandler)
      (crepPrimitive := crepPrimitive) (ffi := ffi) (sharedMem := sharedMem)
      (baseAddress := baseAddress) (topAddress := topAddress)
      (bytesInWord := bytesInWord) (sourceFuel := sourceFuel)
      (targetFuel := targetFuel) (hbody := hbody)
      (hbodySafe := hbodySafe) (hloopSafe := hloopSafe')
      (hbytesInWord := hbytesInWord) (hlookupSource := hlookupSource)
      (hlookupExceptionControl := hlookupExceptionControl) (hpost := hpost)
      (hcode := hcode) (hlookup := hlookup) (hsize := hsize))

end Flapjack
