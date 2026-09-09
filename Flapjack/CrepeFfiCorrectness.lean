import Flapjack.CrepeCorrectness

/-!
Correctness boundary for the FFI part of `pan_to_crep`.

The compiler evaluates the four source arguments into fresh Crepe locals,
executes the external call, and restores those locals when the call returns.
This theorem makes that temporary-state protocol explicit.  The relation
between the source and target handlers is intentionally an assumption: it is
the same semantic boundary at which CakeML leaves `call_FFI` abstract.
-/

namespace Flapjack

def restoreCrepFfiTemps (state original : CrepState α) (offset : Nat) :
    CrepState α :=
  { state with
    locals :=
      restoreCrepLocal
        (restoreCrepLocal
          (restoreCrepLocal
            (restoreCrepLocal state.locals (offset + 4) (original.locals (offset + 4)))
            (offset + 3) (original.locals (offset + 3)))
          (offset + 2) (original.locals (offset + 2)))
        (offset + 1) (original.locals (offset + 1)) }

theorem compile_full_extCall_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (sourceLocals sourceLocals' : VarName → Option α)
    (state state' : CrepState α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (sourceHandler : PanFfiHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (configuration' configurationLength' array' arrayLength' : CrepExp α)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : firstCompiledExp context configuration = some configuration')
    (hconfigurationLength :
      firstCompiledExp context configurationLength = some configurationLength')
    (harray : firstCompiledExp context array = some array')
    (harrayLength : firstCompiledExp context arrayLength = some arrayLength')
    (hconfigurationValue :
      evalCrepFullExp state.locals state.memory baseAddress topAddress
        configuration' = some configurationValue)
    (hconfigurationLengthValue :
      evalCrepFullExp
        (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
        state.memory baseAddress topAddress
        configurationLength' = some configurationLengthValue)
    (harrayValue :
      evalCrepFullExp
        (updateCrepLocal
          (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
          (context.maxVar + 2) configurationLengthValue)
        state.memory baseAddress topAddress
        array' = some arrayValue)
    (harrayLengthValue :
      evalCrepFullExp
        (updateCrepLocal
          (updateCrepLocal
            (updateCrepLocal state.locals (context.maxVar + 1) configurationValue)
            (context.maxVar + 2) configurationLengthValue)
          (context.maxVar + 3) arrayValue)
        state.memory baseAddress topAddress
        arrayLength' = some arrayLengthValue)
    (hsource : evalPanExtCall sourceHandler sourceLocals function
      configuration configurationLength array arrayLength = some sourceLocals')
    (hffi : ffi function configurationValue configurationLengthValue arrayValue
      arrayLengthValue
      ({ state with
        locals :=
          (updateCrepLocal
            (updateCrepLocal
              (updateCrepLocal
                (updateCrepLocal state.locals (context.maxVar + 1)
                  configurationValue)
                (context.maxVar + 2) configurationLengthValue)
              (context.maxVar + 3) arrayValue)
            (context.maxVar + 4) arrayLengthValue) }) = some state') :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 5) state
        (compileProg context
          (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (restoreCrepFfiTemps state' state context.maxVar)) ∧
    evalPanFfiProg sourceHandler sourceLocals
        (.extCall function configuration configurationLength array arrayLength) =
      some sourceLocals' := by
  constructor
  · rw [compileProg_extCall_of_compiled context function configuration
      configurationLength array arrayLength configuration' configurationLength'
      array' arrayLength' hconfiguration hconfigurationLength harray harrayLength]
    simp [nestedDecs, evalCrepFullProg, updateCrepLocal,
      hconfigurationValue, hconfigurationLengthValue, harrayValue,
      harrayLengthValue, hffi, restoreCrepResult, restoreCrepFfiTemps]
  · simpa [evalPanFfiProg] using hsource

/-! The corresponding call equation keeps the lowered handler visible.  The
    caller supplies the result of the full Crepe call evaluator, so this lemma
    can be composed with either the caught- or uncaught-callee contracts in
    `CrepeSemantics`. -/

theorem compile_full_call_handler_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (arguments : List (Exp α)) (compiledArguments : List (CrepExp α))
    (returnShape : Shape) (exception handlerVar : VarName)
    (exceptionCode : α) (handlerProgram : Prog α)
    (handlerNames : List Nat) (result : CrepControlResult α)
    (hfunction : lookupInfo function context.functions =
      some ([], returnShape))
    (hexception : lookupInfo exception context.exceptions = some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress fuel caller
      (some (allocatedNames context returnShape,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments =
      some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (compileProg context
        (.call (some (none, some (exception, handlerVar, handlerProgram)))
          function arguments)) = some result := by
  rw [compileProg_call_handler_of_compiled context function arguments returnShape
    exception handlerVar exceptionCode handlerProgram handlerNames
    compiledArguments hfunction hexception hhandler harguments]
  simpa [evalCrepFullProg] using hcall

def restoreCrepOneTemp (state original : CrepState α) (name : Nat) :
    CrepState α :=
  { state with locals := restoreCrepLocal state.locals name (original.locals name) }

@[simp] theorem restoreCrepLocal_update_same (locals : Nat → Option α)
    (name : Nat) (value : α) (oldValue : Option α) :
    restoreCrepLocal (updateCrepLocal locals name value) name oldValue =
      restoreCrepLocal locals name oldValue := by
  funext current
  by_cases h : current = name <;>
    simp [restoreCrepLocal, updateCrepLocal, h]

/-! Exception production is the other handler-facing lowering in `pan_to_crep`.
The payload is first materialized in a fresh local and then written to the
global return area before the declared exception code is raised. -/

theorem compile_full_raise_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (sourceLocals : VarName → Option α)
    (state : CrepState α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (sourceHandler : PanFfiHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (value : Exp α) (compiledValue : CrepExp α) (sourceValue targetValue : α)
    (hcompile : compileExp context value = ([compiledValue], .one))
    (hexception : lookupInfo exception context.exceptions = some exceptionCode)
    (hvalue : evalPanExp sourceLocals value = some sourceValue)
    (hcompiledValue : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledValue = some targetValue)
    (hpayload : targetValue = sourceValue) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 5) state (compileProg context (.raise exception value)) =
      some (.raised
        (restoreCrepOneTemp
          { state with memory := updateMemory state.memory 0 sourceValue }
          state (context.maxVar + 1)) exceptionCode) ∧
    evalPanProgWithCallsAndFfi [] sourceHandler (fuel + 1) sourceLocals
        (.raise exception value) =
      some (.raised sourceLocals exception sourceValue) := by
  constructor
  · simp [compileProg, hcompile, hexception, freshNames, nestedDecs,
      storeGlobals, crepNestedSeq, evalCrepFullProg, evalCrepFullExp,
      hcompiledValue, hpayload, updateCrepLocal, restoreCrepResult,
      restoreCrepOneTemp]
  · simp [evalPanProgWithCallsAndFfi, hvalue]

/-! Scalar returns are the normal-result counterpart of the raise boundary.
The explicit source/target value equation makes this usable after an FFI or
handler-aware sequence without collapsing the full control result to a list
projection. -/

theorem compile_full_return_simulation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α)
    (sourceLocals : VarName → Option α)
    (state : CrepState α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (sourceHandler : PanFfiHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (value : Exp α) (compiledValue : CrepExp α) (sourceValue targetValue : α)
    (hcompile : compileExp context value = ([compiledValue], .one))
    (hvalue : evalPanExp sourceLocals value = some sourceValue)
    (hcompiledValue : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledValue = some targetValue)
    (hvalueAgreement : targetValue = sourceValue) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state (compileProg context (.return value)) =
      some (.returned state [sourceValue]) ∧
    evalPanProgWithCallsAndFfi [] sourceHandler (fuel + 1) sourceLocals
        (.return value) =
      some (.returned sourceLocals [sourceValue]) := by
  constructor
  · simp [compileProg, hcompile, evalCrepFullProg, evalCrepFullExps,
      hcompiledValue, hvalueAgreement]
  · simp [evalPanProgWithCallsAndFfi, hvalue]

end Flapjack
