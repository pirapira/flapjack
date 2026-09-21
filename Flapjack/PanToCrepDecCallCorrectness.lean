import Flapjack.PanToCrepCorrectnessBridge

namespace Flapjack

/-! Ordinary projection for Cake's successful `DecCall` branch of
    `pc_compile_correct`. The context-coded bridge carries the declaration-call
    shape check, body evaluator equation, caller-local restoration, post-state
    relation, and final clock; this wrapper exposes the ordinary result
    relation without dropping any of those premises. -/
set_option linter.unusedVariables false in
theorem panValuePcCompileCorrect_of_context_code_and_clocked_decCall_returned
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
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext α)
    (clockExceptionRel : ExceptionId → PanValue α → α → Prop)
    (clockExceptionCode : ExceptionId → Option α)
    (clockGlobalsLookup : CrepState α → PanValue α → Option (List α))
    (clockContext : PanValueFfiContext α)
    (clockPrimitive : PanPrimitiveHandler α)
    (clockHandler : PanValueStatefulFfiHandler α σ)
    (clockFunctions : List (FunName × List VarName × Prog α))
    (clockBaseAddress clockTopAddress clockBytesInWord : α)
    (fuel clock callClock finalClock : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue α))
    (clockMemory : α → Option (PanValue α)) (clockFfi : FfiState σ)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (calleeLocals : VarName → Option (PanValue α))
    (nextGlobals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (value : PanValue α) (bodyLocals bodyGlobals : VarName → Option (PanValue α))
    (bodyMemory : α → Option (PanValue α)) (bodyFfi : FfiState σ)
    (targetState : CrepState α)
    (hcall : evalPanValueFfiClockCall clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord fuel clockLocals clockGlobals clockMemory clockFfi clock
      none function arguments =
      some (.control (.returned calleeLocals nextGlobals nextMemory nextFfi
        [value]), callClock))
    (hshape : panShapeMatches (panValueShape clockStructs value) shape = true)
    (hbody : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord fuel
      (updatePanValueMap clockLocals name value) nextGlobals nextMemory nextFfi
      callClock body =
      some (.control (.normal bodyLocals bodyGlobals bodyMemory bodyFfi),
        finalClock))
    (hstate : panValueCrepStateRel clockStructs clockPcContext
      (restorePanValueLocal bodyLocals name (clockLocals name)) bodyGlobals
      bodyMemory targetState) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program ∧
    evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (fuel + 1) clockLocals clockGlobals clockMemory clockFfi
      clock (.decCall name shape function arguments body) =
      some (.control (.normal
        (restorePanValueLocal bodyLocals name (clockLocals name))
        bodyGlobals bodyMemory bodyFfi), finalClock) ∧
    (evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (fuel + 1) clockLocals clockGlobals clockMemory clockFfi
      clock (.decCall name shape function arguments body)).map
      panValueFfiClockResultProjection =
      some (.normal (restorePanValueLocal bodyLocals name (clockLocals name))
        bodyGlobals bodyMemory bodyFfi finalClock) ∧
    panValuePcResultRel clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup
      (.normal (restorePanValueLocal bodyLocals name (clockLocals name))
        bodyGlobals bodyMemory)
      (.normal targetState) := by
  have hcontext :=
    panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_decCall_returned
      program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
      globalsLookup hcompact clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup clockContext clockPrimitive
      clockHandler clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord fuel clock callClock finalClock clockLocals clockGlobals
      clockMemory clockFfi name shape function arguments body calleeLocals
      nextGlobals nextMemory nextFfi value bodyLocals bodyGlobals bodyMemory
      bodyFfi targetState hcall hshape hbody hstate
  have hcorrect := panValuePcCompileCorrect_of_context_code
    sourceEvaluate targetEvaluate codeRel excpRel exceptionCode globalsLookup
    program hcontext.1
  refine ⟨hcorrect, hcontext.2.1, hcontext.2.2.1, ?_⟩
  exact panValuePcResultRel_of_context_code
    clockStructs clockPcContext clockExceptionRel clockExceptionCode
    clockGlobalsLookup
    (.normal (restorePanValueLocal bodyLocals name (clockLocals name))
      bodyGlobals bodyMemory)
    (.normal targetState) hcontext.2.2.2

end Flapjack
