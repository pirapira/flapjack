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

/-! A kernel-checked composition theorem for the stateful source-to-Crep
proof.  `hsourceAdapter` and `htargetAdapter` identify the rich evaluator's
successful result with the existing stateful evaluators.  `hresultLift` is the
explicit remaining obligation for post-state/exception payload and result
representation; because the target compact evaluator has no timeout case,
the theorem does not silently claim the missing clocked/FinalFFI proof. -/
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
    (hresultLift : ∀ (context : CompileContext α) (structs : StructContext)
      (sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceResult : PanValueControlResult α)
      (crepResult : CrepControlResult α)
      (targetResult : CrepPcResult α),
      panValueCrepStateRel structs context sourceInput.locals sourceInput.globals
        sourceInput.memory targetInput.state →
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult →
      crepPcResultOfControl crepResult = some targetResult →
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (panValuePcResultOfControl sourceResult) targetResult) :
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
  have hresult := hresultLift context structs sourceInput targetInput
    exceptionRel sourceResult crepResult targetExecution.result hstate hcontrol
    hcrepShape
  simpa [hsourceShape] using hresult

end Flapjack
