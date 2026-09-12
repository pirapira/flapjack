import Flapjack.CrepeArgumentCorrectness
import Flapjack.CrepeCallReturnedCorrectness

/-!
Argument preparation for recursively correct returned ordinary calls.

The returned-call composition theorem already handles callee state transport
and control-result relation.  This adapter supplies its flattened argument
evaluation witness from the source expression contract.
-/

namespace Flapjack

theorem compile_full_pan_value_call_returned_of_expression_correct
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
    (sourceValues : List (PanValue α))
    (argumentValues : List α)
    (hargumentValues : argumentValues =
      argumentValuesSource.flatMap panValueFlatWords)
    (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (targetValues : List α) (targetParameters : List Nat)
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
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.returned targetCallee targetValues))
    (hcompileArguments : compileArgs context arguments = compiledArguments)
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
  exact compile_full_pan_value_call_returned_of_body_correct
    context calleeContext structs sourceFunctions functions sourceGlobals caller
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel function compiledArguments sourceCalleeLocals
    sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceCalleeMemory sourceValues
    argumentValues targetCalleeLocals targetCallee target targetValues
    targetParameters sourceBody targetBody exceptionRel hbodyCorrect hrelCallee
    hsourceBody hcompileBody hcrepBody hcompiledTarget hlookup hassign hcrepCall

theorem compile_full_pan_value_call_state_returned_of_expression_correct
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
      PanValueCrepExpressionStateCorrect expression)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory caller)
    (hsourceArguments : evalPanValueExps structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord arguments =
      some argumentValuesSource)
    (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceValues : List (PanValue α))
    (argumentValues : List α)
    (hargumentValues : argumentValues =
      argumentValuesSource.flatMap panValueFlatWords)
    (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (targetValues : List α) (targetParameters : List Nat)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbodyCorrect : PanValueCrepProgramStateCorrect sourceBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceCalleeMemory
      { locals := targetCalleeLocals, memory := caller.memory,
        globals := caller.globals })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceCalleeMemory sourceBody =
      some (.returned sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceValues))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory,
        globals := caller.globals } targetBody =
      some (.returned targetCallee targetValues))
    (hcompileArguments : compileArgs context arguments = compiledArguments)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) targetParameters argumentValues =
      some targetCalleeLocals)
    (hcrepCall : evalCrepFullCallState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller none function
      compiledArguments = some (.returned target targetValues)) :
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceCalleeGlobals sourceCalleeMemory sourceValues)
      (.returned target targetValues) := by
  obtain ⟨compiled, hcompile, hcompiled⟩ :=
    compileArgs_evalCrepFullExpsState_of_expression_correct context structs
      sourceLocals sourceGlobals sourceMemory caller
      baseAddress topAddress bytesInWord arguments argumentValuesSource hexpression
      hstate hsourceArguments
  have hsame : compiled = compiledArguments := hcompile.symm.trans hcompileArguments
  subst compiled
  have hcompiledTarget :
      evalCrepFullExpsState caller baseAddress topAddress compiledArguments =
        some argumentValues := by
    rw [← hcompileArguments]
    simpa [hargumentValues] using hcompiled
  exact compile_full_pan_value_call_state_returned_of_body_correct
    context calleeContext structs sourceFunctions functions sourceGlobals caller
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel function compiledArguments sourceCalleeLocals
    sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory sourceCalleeMemory
    sourceValues argumentValues targetCalleeLocals targetCallee target targetValues
    targetParameters sourceBody targetBody exceptionRel hbodyCorrect hrelCallee
    hsourceBody hcompileBody hcrepBody hcompiledTarget hlookup hassign hcrepCall

end Flapjack
