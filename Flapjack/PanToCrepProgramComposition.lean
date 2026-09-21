import Flapjack.PanToCrepCorrectnessBridge

namespace Flapjack

/-! Program-level composition for the Lean analogue of Cake's
    `pc_compile_correct`.  The paired state-correctness/control-safety
    constructor induction is composed with the compact state-evidence
    boundary so that constructor-level branch obligations for the whole
    program yield `PanValuePcCompileCorrect` for every source     program. -/
set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_of_state_and_control_safe_induction
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (hskip : PanValueCrepProgramStateCorrect (.skip : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.skip : Prog α))
    (hdec : ∀ (name : VarName) (shape : Shape) (value : Exp α)
      (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.dec name shape value body) ∧
        PanValueCrepProgramStateControlSafe (.dec name shape value body))
    (hassign : ∀ (kind : VarKind) (name : VarName) (value : Exp α),
      PanValueCrepProgramStateCorrect (.assign kind name value) ∧
        PanValueCrepProgramStateControlSafe (.assign kind name value))
    (hprimitive : ∀ (name : VarName) (operator : PrimOp)
      (args : List (Exp α)),
      PanValueCrepProgramStateCorrect (.primitive name operator args) ∧
        PanValueCrepProgramStateControlSafe (.primitive name operator args))
    (hstore : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.store address value) ∧
        PanValueCrepProgramStateControlSafe (.store address value))
    (hstore32 : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.store32 address value) ∧
        PanValueCrepProgramStateControlSafe (.store32 address value))
    (hstoreByte : ∀ (address value : Exp α),
      PanValueCrepProgramStateCorrect (.storeByte address value) ∧
        PanValueCrepProgramStateControlSafe (.storeByte address value))
    (hseq : ∀ (first second : Prog α),
      (PanValueCrepProgramStateCorrect first ∧
        PanValueCrepProgramStateControlSafe first) →
      (PanValueCrepProgramStateCorrect second ∧
        PanValueCrepProgramStateControlSafe second) →
      PanValueCrepProgramStateCorrect (.seq first second) ∧
        PanValueCrepProgramStateControlSafe (.seq first second))
    (hite : ∀ (condition : Exp α) (thenBranch elseBranch : Prog α),
      (PanValueCrepProgramStateCorrect thenBranch ∧
        PanValueCrepProgramStateControlSafe thenBranch) →
      (PanValueCrepProgramStateCorrect elseBranch ∧
        PanValueCrepProgramStateControlSafe elseBranch) →
      PanValueCrepProgramStateCorrect (.ite condition thenBranch elseBranch) ∧
        PanValueCrepProgramStateControlSafe (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : Exp α) (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.while condition body) ∧
        PanValueCrepProgramStateControlSafe (.while condition body))
    (hbreak : PanValueCrepProgramStateCorrect (.break : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.break : Prog α))
    (hcontinue : PanValueCrepProgramStateCorrect (.continue : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.continue : Prog α))
    (hcall : ∀
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (name : FunName) (args : List (Exp α)),
      (match info with
       | some (_, some (_, _, handler)) =>
           PanValueCrepProgramStateCorrect handler ∧
             PanValueCrepProgramStateControlSafe handler
       | _ => True) →
      PanValueCrepProgramStateCorrect (.call info name args) ∧
        PanValueCrepProgramStateControlSafe (.call info name args))
    (hdecCall : ∀ (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α),
      (PanValueCrepProgramStateCorrect body ∧
        PanValueCrepProgramStateControlSafe body) →
      PanValueCrepProgramStateCorrect (.decCall name shape function args body) ∧
        PanValueCrepProgramStateControlSafe (.decCall name shape function args body))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Exp α),
      PanValueCrepProgramStateCorrect
          (.extCall function configuration configurationLength array arrayLength) ∧
        PanValueCrepProgramStateControlSafe
          (.extCall function configuration configurationLength array arrayLength))
    (hraise : ∀ (exception : ExceptionId) (value : Exp α),
      PanValueCrepProgramStateCorrect (.raise exception value) ∧
        PanValueCrepProgramStateControlSafe (.raise exception value))
    (hreturn : ∀ (value : Exp α),
      PanValueCrepProgramStateCorrect (.return value) ∧
        PanValueCrepProgramStateControlSafe (.return value))
    (hshMemLoad : ∀ (size : OpSize) (kind : VarKind) (name : VarName)
      (address : Exp α),
      PanValueCrepProgramStateCorrect (.shMemLoad size kind name address) ∧
        PanValueCrepProgramStateControlSafe (.shMemLoad size kind name address))
    (hshMemStore : ∀ (size : OpSize) (address value : Exp α),
      PanValueCrepProgramStateCorrect (.shMemStore size address value) ∧
        PanValueCrepProgramStateControlSafe (.shMemStore size address value))
    (htick : PanValueCrepProgramStateCorrect (.tick : Prog α) ∧
      PanValueCrepProgramStateControlSafe (.tick : Prog α))
    (hannot : ∀ (tag text : String),
      PanValueCrepProgramStateCorrect (@Prog.annot α tag text) ∧
        PanValueCrepProgramStateControlSafe (@Prog.annot α tag text))
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
    (hpost : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState)
    (hcode : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    ∀ program : Prog α,
      PanValuePcCompileCorrect
        (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
          baseAddress topAddress bytesInWord sourceFuel)
        (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
          baseAddress topAddress targetFuel)
        codeRel excpRel exceptionCode globalsLookup program := by
  intro program
  obtain ⟨hprogram, hprogramSafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_induction
      hskip hdec hassign hprimitive hstore hstore32 hstoreByte hseq hite hwhile
      hbreak hcontinue hcall hdecCall hextCall hraise hreturn hshMemLoad
      hshMemStore htick hannot program
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hpost hcode hlookup hsize

/-! The fully generic composition above demands all twenty-one constructor
    branch hypotheses.  For the `StatefulCompactProg` fragment the paired
    state-correctness/control-safety facts are already kernel-checked, so the
    context-coded evaluator boundary can be instantiated without any branch
    hypotheses.  The four raised-state premises and the exception-lookup
    premise stay explicit, exactly as on the generic boundary. -/
set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_statefulCompact_context_code
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (hprogram : StatefulCompactProg α program)
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
    (hlookupException : ∀ (context : CompileContext α)
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
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState)
    (hcode : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  obtain ⟨hcorrect, hsafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_statefulCompact program
      hprogram
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hcorrect hsafe hlookupException hpost hcode
    hlookup hsize

set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_compact_statefulCompact
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (hprogram : StatefulCompactProg α program)
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
    (hpost : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState)
    (hcode : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      exceptionCode sourceException = some targetException)
    (hlookup : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue))
    (hsize : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α) (targetException : α),
      Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  obtain ⟨hcorrect, hsafe⟩ :=
    panValueCrepProgramStateCorrect_and_controlSafe_statefulCompact program
      hprogram
  exact panValuePcCompileCorrect_compact_with_raised_state_evidence
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hcorrect hsafe hpost hcode hlookup hsize

end Flapjack
