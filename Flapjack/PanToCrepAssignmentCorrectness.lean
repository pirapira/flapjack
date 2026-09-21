import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.CrepeProgramAssignmentCorrectness

namespace Flapjack

theorem panValueCrepProgramStateControlSafe_assign_local
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (value : Exp α) :
    PanValueCrepProgramStateControlSafe (.assign .local name value) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  exact panValuePcControlLabelSafe_of_not_broke_continued sourceResult crepResult
    (PanValueProgNotBrokeContinued_assign_local primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord name value
      sourceFuel sourceLocals sourceGlobals sourceMemory sourceResult hsource)

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_assign_local_source_word_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (expression : SourceWordExp α)
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
    (hdirect : ∀ (context : CompileContext α) (compiled : CrepExp α)
      (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      compileExp context expression.toExp = ([compiled], .one) →
      distinctLists [slot] (crepExpVars compiled) = true)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (oldValue : PanValue α),
      sourceLocals name = some oldValue →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupAll : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (localName : VarName) (localValue : PanValue α),
      sourceLocals localName = some localValue →
      ∃ slot, lookupInfo localName context.vars = some (.one, [slot]))
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hnoalias : ∀ (context : CompileContext α) (slot : Nat),
      lookupInfo name context.vars = some (.one, [slot]) →
      ∀ oldName oldShape oldSlots,
        oldName ≠ name →
        lookupInfo oldName context.vars = some (oldShape, oldSlots) →
        slot ∉ oldSlots)
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
    (hlookupGlobal : ∀ (context : CompileContext α) (structs : StructContext)
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
      (.assign .local name expression.toExp) := by
  have hprogram := panValueCrepProgramStateCorrect_assign_local_source_word_direct
    name expression hdirect hlookup hlookupAll hbytesInWord hnoalias
  have hprogramSafe := panValueCrepProgramStateControlSafe_assign_local
    name expression.toExp
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.assign .local name expression.toExp) codeRel excpRel exceptionCode
    globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
    ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
    hprogram hprogramSafe hpost hcode hlookupGlobal hsize

end Flapjack
