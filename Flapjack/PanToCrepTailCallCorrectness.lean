import Flapjack.PanToCrepCorrectnessBridge
import Flapjack.PanSimpEvaluate

/-!
The `Call_TailCall` branch of CakeML's `pan_to_crepProofScript.sml`
`pc_compile_correct` (line 3182).  Cake rewrites an assign-and-return call

  `AssignCall x (Call f args); Return (Var x)`

through `seq_call_ret` into the destination-free call `Call NONE f args`, then
uses `evaluate_seq_call_ret_eq` to transport the evaluator result.  This file
provides the corresponding context-coded bridge for the Flapjack port: it ties
the syntactic fusion `seqCallRet` (via `seqCallRet_tail_call`) and the clocked
evaluator equation `evalPanValueFfiClockProg_seq_call_return_tail_call` to the
destination-free Crep call.  All evaluator/state/code premises stay explicit.
-/

namespace Flapjack

/-- Context-coded `Call_TailCall` bridge.  Given the destination-free tail call
    evaluates to the returned value (the `hTailCall` premise) and the explicit
    evaluator premises that make `seq_call_ret` sound, the original
    destination-call-then-return sequence evaluates to the same returned value,
    its projection is the same projected result, and the context-coded result
    relation therefore transports to the sequence shape. -/
theorem panValuePcCompileCorrectWithContextCode_of_context_code_and_clocked_call_tailCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α) (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α) (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hcompact : PanValuePcCompileCorrectWithContextCode sourceEvaluate
      targetEvaluate codeRel excpRel exceptionCode globalsLookup program)
    (clockStructs : StructContext) (clockPcContext : CompileContext α)
    (clockExceptionRel : ExceptionId → PanValue α → α → Prop)
    (clockExceptionCode : ExceptionId → Option α)
    (clockGlobalsLookup : CrepState α → PanValue α → Option (List α))
    (clockContext : PanValueFfiContext α) (clockPrimitive : PanPrimitiveHandler α)
    (clockHandler : PanValueStatefulFfiHandler α σ)
    (clockFunctions : List (FunName × List VarName × Prog α))
    (clockBaseAddress clockTopAddress clockBytesInWord : α)
    (fuel clock finalClock : Nat) (hclock : clock ≠ 0)
    (clockLocals clockGlobals : VarName → Option (PanValue α))
    (clockMemory : α → Option (PanValue α)) (clockFfi : FfiState σ)
    (value : PanValue α) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (returnName : VarName) (assignedLocals : VarName → Option (PanValue α))
    (hTailCall : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress clockBytesInWord
      (fuel + 3) clockLocals clockGlobals clockMemory clockFfi clock
      (.call none function arguments) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi
        [value]), finalClock))
    (hargs : evalPanValueExps clockStructs clockLocals clockGlobals clockMemory
      clockBaseAddress clockTopAddress clockBytesInWord arguments = some [value])
    (hlookup : lookupPanFunction function clockFunctions = some (parameters, body))
    (hbind : bindPanValueParameters parameters [value] = some calleeLocals)
    (hbody : evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress clockBytesInWord
      fuel calleeLocals clockGlobals clockMemory clockFfi (clock - 1) body =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi
        [value]), finalClock))
    (hwithin : panValueValuesWithinLimit clockStructs [value] = true)
    (hpayload : panValuePayloadWithinLimit clockStructs value = true)
    (hassign : assignPanValueCallResult clockLocals finalGlobals
      (some (.local, returnName)) [value] (structs := clockStructs) =
      some (assignedLocals, finalGlobals))
    (hlookupReturn : assignedLocals returnName = some value)
    (targetState : CrepState α) (targetValues : List α)
    (hstate : panValueCrepStateRel clockStructs clockPcContext (fun _ => none)
      finalGlobals finalMemory targetState)
    (hvalues : panValueCrepValuesRel [value] targetValues) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate codeRel
      excpRel exceptionCode globalsLookup program ∧
    evalPanValueFfiClockProg clockContext clockPrimitive clockHandler clockStructs
      clockFunctions clockBaseAddress clockTopAddress clockBytesInWord (fuel + 3)
      clockLocals clockGlobals clockMemory clockFfi clock
      (.seq (.call (some (some (.local, returnName), none)) function arguments)
        (.return (.var .local returnName))) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi
        [value]), finalClock) ∧
    (evalPanValueFfiClockProg clockContext clockPrimitive clockHandler clockStructs
      clockFunctions clockBaseAddress clockTopAddress clockBytesInWord (fuel + 3)
      clockLocals clockGlobals clockMemory clockFfi clock
      (.seq (.call (some (some (.local, returnName), none)) function arguments)
        (.return (.var .local returnName)))).map panValueFfiClockResultProjection =
      some (.returned (fun _ => none) finalGlobals finalMemory finalFfi [value]
        finalClock) ∧
    panValuePcResultRelWithContextCode clockStructs clockPcContext clockExceptionRel
      clockExceptionCode clockGlobalsLookup
      (.returned (fun _ => none) finalGlobals finalMemory [value])
      (.returned targetState targetValues) := by
  have hEq := evalPanValueFfiClockProg_seq_call_return_tail_call clockContext
    clockPrimitive clockHandler clockStructs clockFunctions clockBaseAddress
    clockTopAddress clockBytesInWord fuel clock finalClock hclock clockLocals
    clockGlobals clockMemory clockFfi value parameters calleeLocals bodyLocals
    finalGlobals finalMemory finalFfi body function arguments returnName
    assignedLocals none hargs hlookup hbind hbody hwithin hpayload hassign hlookupReturn
  refine ⟨hcompact, ?_, ?_, ?_⟩
  · rw [← hEq]
    exact hTailCall
  · rw [← hEq, hTailCall]
    rfl
  · simp [panValuePcResultRelWithContextCode, panValuePcResultRel, hstate, hvalues]

/-- Syntactic counterpart used by the `Call_TailCall` branch: the `seqCallRet`
    fusion of the assign-and-return call is exactly the destination-free call. -/
theorem seqCallRet_tailCall_shape (returnName : VarName) (function : FunName)
    (arguments : List (Exp α)) :
    seqCallRet
        (.seq (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnName))) =
      .call none function arguments :=
  seqCallRet_tail_call returnName function arguments

end Flapjack
