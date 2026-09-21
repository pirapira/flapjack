import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.PanToCrepSharedMemoryControlSafety

/-!
# Source-word shared-memory correctness wrappers

These are the high-level counterparts of the `ShMemLoad` and `ShMemStore`
branches in CakeML Pancake's `pc_compile_correct` proof.  The lower-level
state-correctness lemmas describe the shared-memory transition explicitly;
these wrappers package them with the generic raised-state result boundary.
Global shared-memory loads remain outside this interface because Pancake's
`localisedProg` premise excludes them and Flapjack's compiler lowers them to
`skip`, matching that supported subset.
-/

namespace Flapjack

/-! Direct result-relation bridge for the local shared-memory load.  This is
the form closest to Pancake's individual `pc_compile_correct[ShMemLoad]`
branch: the raised-result relation is supplied as one explicit premise while
the source/Crep leaf simulation is discharged by the source-word constructor. -/

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

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_shMemLoad_source_word_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (name : VarName) (address : SourceWordExp α)
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
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookupSource : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
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
      (.shMemLoad size .local name address.toExp) := by
  obtain ⟨hprogram, hprogramSafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_shMemLoad_source_word
      size name address hbytesInWord hlookupSource hsharedRel
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.shMemLoad size .local name address.toExp) codeRel excpRel exceptionCode
    globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
    ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
    hprogram hprogramSafe hpost hcode hlookup hsize

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_shMemStore_source_word_of_state_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (size : OpSize) (address value : SourceWordExp α)
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
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookupSource : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value)
    (hsharedRel : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (state targetState : CrepState α) (_crepPrimitive : CrepPrimitiveHandler α)
      (_ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
      (_baseAddress _topAddress _bytesInWord addressValue valueValue : α)
      (temporary : Nat),
      sharedMem (storeMemOp size) temporary addressValue
          { state with
            locals := updateCrepLocal state.locals temporary valueValue } =
        some targetState →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        (updatePanValueMemory sourceMemory addressValue (.word valueValue))
        { targetState with
          locals := restoreCrepLocal targetState.locals
            temporary (state.locals temporary) })
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
      (.shMemStore size address.toExp value.toExp) := by
  obtain ⟨hprogram, hprogramSafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_shMemStore_source_word
      size address value hbytesInWord hlookupSource hstable hsharedRel
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    (.shMemStore size address.toExp value.toExp) codeRel excpRel exceptionCode
    globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
    ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
    hprogram hprogramSafe hpost hcode hlookup hsize

end Flapjack
