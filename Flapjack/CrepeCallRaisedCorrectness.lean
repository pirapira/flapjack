import Flapjack.CrepeCallControlTransport
import Flapjack.CrepeProgramRelation

/-!
Recursive correctness composition for an ordinary raised call.

The callee body relation is preserved when an uncaught exception is propagated
through an ordinary call: the caller locals are retained and the callee memory
is exposed to the caller.
-/

namespace Flapjack

theorem compile_full_pan_value_call_raised_of_body_correct
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
    (function : FunName) (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (argumentValues : List α) (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (crepException : α)
    (destinations : Option (List Nat))
    (targetParameters : List Nat)
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
      some (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory } targetBody =
      some (.raised targetCallee crepException))
    (hcrepArguments : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) targetParameters argumentValues =
      some targetCalleeLocals)
    (hcrepCall : evalCrepFullCall functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
        (destinations.map (fun ds => (ds, (none : Option (α × CrepProg α))))) function
      compiledArguments = some (.raised target crepException)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (.raised target crepException) := by
  have hcrepBody' : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory }
      (compileProg calleeContext sourceBody) =
      some (.raised targetCallee crepException) := by
    rw [hcompileBody]
    exact hcrepBody
  have hbodyRel := hbodyCorrect calleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := caller.memory }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
      sourceException sourceValue)
    (.raised targetCallee crepException)
    hrelCallee hsourceBody hcrepBody'
  have htarget :
      { caller with memory := targetCallee.memory } = target := by
    have hsome :
        some (CrepControlResult.raised
          { caller with memory := targetCallee.memory } crepException) =
          some (CrepControlResult.raised target crepException) := by
      cases destinations with
      | none =>
          simpa [evalCrepFullCall, hcrepArguments, hlookup, hassign, hcrepBody]
            using hcrepCall
      | some destinations =>
          simpa [evalCrepFullCall, hcrepArguments, hlookup, hassign, hcrepBody]
            using hcrepCall
    have hresult := Option.some.inj hsome
    injection hresult
  have hcallRel := panValueCrepControlRel_call_raised_of_contexts
    structs calleeContext context exceptionRel
    sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals
    targetCallee caller.locals sourceException sourceValue crepException hbodyRel
  cases htarget
  exact hcallRel

theorem compile_full_pan_value_call_state_raised_of_body_correct
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
    (function : FunName) (compiledArguments : List (CrepExp α))
    (sourceCalleeLocals sourceBodyLocals : VarName → Option (PanValue α))
    (sourceCalleeGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceCalleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (argumentValues : List α) (targetCalleeLocals : Nat → Option α)
    (targetCallee : CrepState α) (target : CrepState α)
    (crepException : α)
    (destinations : Option (List Nat))
    (targetParameters : List Nat)
    (sourceBody : Prog α) (targetBody : CrepProg α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbodyCorrect : PanValueCrepProgramStateCorrect sourceBody)
    (hrelCallee : panValueCrepStateRel structs calleeContext
      sourceCalleeLocals sourceGlobals sourceMemory
      { locals := targetCalleeLocals, memory := caller.memory,
        globals := caller.globals })
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceCalleeLocals sourceGlobals sourceMemory sourceBody =
      some (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue))
    (hcompileBody : compileProg calleeContext sourceBody = targetBody)
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory,
        globals := caller.globals } targetBody =
      some (.raised targetCallee crepException))
    (hcrepArguments : evalCrepFullExpsState caller baseAddress topAddress
      compiledArguments = some argumentValues)
    (hlookup : lookupCompiledFunction function functions =
      some (targetParameters, targetBody))
    (hassign : assignCrepValues (fun _ => none) targetParameters argumentValues =
      some targetCalleeLocals)
    (hcrepCall : evalCrepFullCallState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) caller
        (destinations.map (fun ds => (ds, (none : Option (α × CrepProg α))))) function
      compiledArguments = some (.raised target crepException)) :
    panValueCrepControlRel structs context exceptionRel
      (.raised (fun _ => none) sourceCalleeGlobals sourceCalleeMemory
        sourceException sourceValue)
      (.raised target crepException) := by
  have hcrepBody' : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel
      { locals := targetCalleeLocals, memory := caller.memory,
        globals := caller.globals }
      (compileProg calleeContext sourceBody) =
      some (.raised targetCallee crepException) := by
    rw [hcompileBody]
    exact hcrepBody
  have hbodyRel := hbodyCorrect calleeContext structs sourceFunctions functions
    sourceCalleeLocals sourceGlobals sourceMemory
    { locals := targetCalleeLocals, memory := caller.memory,
      globals := caller.globals }
    primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    (.raised sourceBodyLocals sourceCalleeGlobals sourceCalleeMemory
      sourceException sourceValue)
    (.raised targetCallee crepException)
    hrelCallee hsourceBody hcrepBody'
  have htarget :
      { locals := caller.locals, memory := targetCallee.memory,
        globals := targetCallee.globals } = target := by
    have hsome :
        some (CrepControlResult.raised
          { locals := caller.locals, memory := targetCallee.memory,
            globals := targetCallee.globals } crepException) =
          some (CrepControlResult.raised target crepException) := by
      cases destinations with
      | none =>
          simpa [evalCrepFullCallState, hcrepArguments, hlookup, hassign, hcrepBody]
            using hcrepCall
      | some destinations =>
          simpa [evalCrepFullCallState, hcrepArguments, hlookup, hassign, hcrepBody]
            using hcrepCall
    have hresult := Option.some.inj hsome
    injection hresult
  have hcallRel := panValueCrepControlRel_call_raised_of_contexts
    structs calleeContext context exceptionRel
    sourceCalleeGlobals sourceCalleeMemory sourceBodyLocals
    targetCallee caller.locals sourceException sourceValue crepException hbodyRel
  cases htarget
  exact hcallRel

end Flapjack
