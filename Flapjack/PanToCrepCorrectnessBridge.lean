import Flapjack.PanToCrepCorrectnessBoundary

/-!
Bridge from the existing stateful source-to-Crep program correctness contract
to the exact `pc_compile_correct` boundary.  This theorem is intentionally
adapter-parametric: the stateful evaluator already proves the five compact
control cases, while the adapters and result lift must account for the
clocked `TimeOut` and `FinalFFI` cases before a concrete top-level evaluator
can instantiate the full boundary.
-/

namespace Flapjack

def panValuePcResultOfControl :
    PanValueControlResult α → PanValuePcResult α
  | .normal locals globals memory => .normal locals globals memory
  | .returned locals globals memory values =>
      .returned locals globals memory values
  | .raised locals globals memory exception value =>
      .raised locals globals memory exception value
  | .broke locals globals memory => .broke locals globals memory
  | .continued locals globals memory => .continued locals globals memory

def crepPcResultOfControl :
    CrepControlResult α → Option (CrepPcResult α)
  | .normal state => some (.normal state)
  | .returned state values => some (.returned state values)
  | .raised state exception => some (.raised state exception)
  | .broke state label => some (.broke state label)
  | .continued state label => some (.continued state label)
  | .finalFfi _ _ => none

/-! The ordinary compact control cases are proved directly from the existing
`panValueCrepControlRel`.  Only the raised payload needs an additional
obligation because the exact Pc relation retains both the HOL post-state
relation and the exception-code/global-payload clause. -/
theorem panValuePcResultRel_of_control
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hraise : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
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
        targetState targetException)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (targetResult : CrepPcResult α)
    (hcontrol : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult)
    (hresult : crepPcResultOfControl crepResult = some targetResult) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (panValuePcResultOfControl sourceResult) targetResult := by
  cases sourceResult with
  | normal sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | normal targetState =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | returned _ _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | returned sourceLocals sourceGlobals sourceMemory sourceValues =>
      cases crepResult with
      | returned targetState targetValues =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue =>
      cases crepResult with
      | raised targetState targetException =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using
            (hraise sourceLocals sourceGlobals sourceMemory sourceException
              sourceValue targetState targetException hcontrol)
      | normal _ | returned _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | broke sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | broke targetState targetLabel =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | continued sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | continued targetState targetLabel =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | broke _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol

/-! A kernel-checked composition theorem for the stateful source-to-Crep
proof.  `hsourceAdapter` and `htargetAdapter` identify the rich evaluator's
successful result with the existing stateful evaluators.  Ordinary
normal/return/break/continue results are then proved by
`panValuePcResultRel_of_control`; only the raised payload/state clause is an
explicit obligation.  Because the target compact evaluator has no timeout
case, the theorem does not silently claim the missing clocked/FinalFFI proof.
-/
theorem panValuePcCompileCorrect_of_stateful_program
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
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
    (hprogram : PanValueCrepProgramStateCorrect program)
    (hsourceAdapter : ∀ (context : CompileContext α)
      (structs : StructContext) (sourceInput : PanValuePcInput α)
      (_targetInput : CrepPcInput α)
      (sourceExecution : PanValuePcExecution α),
      sourceEvaluate context sourceInput program = some sourceExecution →
      ∃ sourceResult,
        evalPanValueProgWithPrimitiveCallsAndFfi
          primitive sourceHandler structs sourceFunctions
          baseAddress topAddress bytesInWord sourceFuel
          sourceInput.locals sourceInput.globals sourceInput.memory program =
            some sourceResult ∧
        sourceExecution.result = panValuePcResultOfControl sourceResult)
    (htargetAdapter : ∀ (context : CompileContext α)
      (_structs : StructContext) (_sourceInput : PanValuePcInput α)
      (targetInput : CrepPcInput α) (targetExecution : CrepPcExecution α),
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      ∃ crepResult,
        evalCrepFullProgState functions crepPrimitive ffi sharedMem
          baseAddress topAddress targetFuel targetInput.state
          (compileProg context program) = some crepResult ∧
        crepPcResultOfControl crepResult = some targetExecution.result)
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
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hdistinct hlocalisedCode hlocalised hcode hexcp hstate
    hnonerror hsource htarget hpostCode hpostExcp
  obtain ⟨sourceResult, hsourceResult, hsourceShape⟩ :=
    hsourceAdapter context structs sourceInput targetInput sourceExecution hsource
  obtain ⟨crepResult, hcrepResult, hcrepShape⟩ :=
    htargetAdapter context structs sourceInput targetInput targetExecution htarget
  have hcontrol := hprogram context structs sourceFunctions functions
    sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
    hstate hsourceResult hcrepResult
  have hresult := panValuePcResultRel_of_control structs context exceptionRel
    exceptionCode globalsLookup (hraise context structs exceptionRel)
    sourceResult crepResult targetExecution.result hcontrol hcrepShape
  simpa [hsourceShape] using hresult

end Flapjack
