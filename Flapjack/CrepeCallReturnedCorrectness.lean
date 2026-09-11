import Flapjack.CrepeCallControlTransport
import Flapjack.CrepeProgramRelation

/-!
Recursive correctness composition for an ordinary returned call.

The source and target callee-body evaluations are supplied at their
respective compile contexts.  The recursive program-correctness hypothesis
relates those body results, and ordinary-call transport changes the callee
state to the caller-local/callee-memory result observed by the caller.
-/

namespace Flapjack

theorem compile_full_pan_value_call_returned_of_body_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context calleeContext : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceGlobals : VarName → Option (PanValue α))
    (caller : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (function : FunName)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValues : List (PanValue α))
    (argumentValues : List α)
    (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (targetValues : List α) (targetParameters : List Nat)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbodyCorrect : PanValueCrepProgramCorrect sourceBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := caller.memory })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceMemory sourceBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.returned targetCallee targetValues))
    (hcrepArguments : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) targetParameters argumentValues =
      some targetCalleeLocals)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller none function
      compiledArguments = some (.returned target targetValues)) :
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory sourceValues)
      (.returned target targetValues) := by
  have hcrepBody' : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory }
      (compileProg calleeContext sourceBody) =
      some (.returned targetCallee targetValues) := by
    rw [hcompileBody]
    exact hcrepBody
  have hbodyRel := hbodyCorrect calleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := caller.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceValues)
    (.returned targetCallee targetValues)
    hrelCallee hsourceBody hcrepBody'
  have htarget :
      { caller with memory := targetCallee.memory } = target := by
    have hsome :
        some (CrepControlResult.returned
          { caller with memory := targetCallee.memory } targetValues) =
          some (CrepControlResult.returned target targetValues) := by
      simpa [evalCrepFullCall, hcrepArguments, hlookup, hassign, hcrepBody]
        using hcrepCall
    have hresult := Option.some.inj hsome
    injection hresult
  have hcallRel := panValueCrepControlRel_call_returned_of_contexts
    structs calleeContext context exceptionRel
    sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals targetCallee
    caller.locals sourceValues targetValues hbodyRel
  cases htarget
  exact hcallRel

end Flapjack
