import Flapjack.CrepeArgumentCorrectness
import Flapjack.CrepeCallRaisedCorrectness

/-!
Argument preparation for recursively correct raised ordinary calls.

This is the exceptional counterpart of the returned-call adapter.  It derives
the flattened argument witness from the source expression contract and then
delegates exception propagation and callee-memory transport to the recursive
call theorem.
-/

namespace Flapjack

theorem compile_full_pan_value_call_raised_of_expression_correct
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context calleeContext : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals : VarName → Option (PanValue α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (caller : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (function : FunName)
    (arguments : List (Exp α))
    (argumentValuesSource : List (PanValue α))
    (hexpression : ∀ expression ∈ arguments,
      PanValueCrepExpressionCorrect expression)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory caller)
    (hsourceArguments : evalPanValueExps structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord arguments =
      some argumentValuesSource)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (argumentValues : List α)
    (hargumentValues : argumentValues =
      argumentValuesSource.flatMap panValueFlatWords)
    (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (crepException : α) (targetParameters : List Nat)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbodyCorrect : PanValueCrepProgramCorrect sourceBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceCalleeMemory
      { locals := targetCalleeLocals, memory := caller.memory })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceCalleeMemory sourceBody =
      some (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.raised targetCallee crepException))
    (hcompileArguments : compileArgs context arguments = compiledArguments)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) targetParameters argumentValues =
      some targetCalleeLocals)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller none function
      compiledArguments = some (.raised target crepException)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (.raised target crepException) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileArgs_evalCrepFullExps_of_expression_correct context structs
      sourceLocals sourceGlobals sourceMemory caller
      baseAddress topAddress bytesInWord arguments argumentValuesSource hexpression
      hstate hsourceArguments
  have hsame : compiled = compiledArguments := hcompile.symm.trans hcompileArguments
  subst compiled
  have hcompiledTarget :
      evalCrepFullExps caller.locals caller.memory baseAddress topAddress
        compiledArguments = some argumentValues := by
    rw [← hcompileArguments]
    simpa [hargumentValues] using hcompiled
  exact compile_full_pan_value_call_raised_of_body_correct
    context calleeContext structs sourceFunctions functions sourceGlobals caller
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel function compiledArguments sourceCalleeLocals
    sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceException sourceValue
    argumentValues targetCalleeLocals targetCallee target crepException
    targetParameters sourceBody targetBody exceptionRel hbodyCorrect hrelCallee
    hsourceBody hcompileBody hcrepBody hcompiledTarget hlookup hassign hcrepCall

end Flapjack
