import Flapjack.CrepeCorrectness

/-!
Source-side evaluator equations for ordinary calls whose callee exception is
caught by the call's handler metadata.  The Crep evaluator already exposes
the corresponding equation in `CrepeSemantics`; keeping the source rule
explicit prevents caught calls from being treated as an opaque relation
witness in the eventual program induction.
-/

namespace Flapjack

theorem evalPanValueCall_caught_handler_of_eval
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (contracts : Option PanValueCallContracts)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (body : Prog α) (calleeLocals : VarName → Option (PanValue α))
    (calleeBodyLocals : VarName → Option (PanValue α))
    (calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (destination : Option (VarKind × VarName))
    (caught : ExceptionId) (handlerVariable : VarName)
    (handlerProgram : Prog α) (sourceResult : PanValueControlResult α)
    (hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hcallee : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord fuel
      calleeLocals sourceGlobals sourceMemory body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.raised calleeBodyLocals calleeGlobals calleeMemory
        sourceException sourceValue))
    (hexception : panValueExceptionValid structs contracts
      sourceException sourceValue = true)
    (hpayload : panValuePayloadWithinLimit structs sourceValue = true)
    (hcaught : caught == sourceException)
    (hhandlerValid : panValueHandlerValid structs contracts sourceLocals
      handlerVariable sourceValue = true)
    (hhandler : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord fuel
      (updatePanValueMap sourceLocals handlerVariable sourceValue)
      calleeGlobals calleeMemory handlerProgram
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult) :
    evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs functions baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (some (destination, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult := by
  have hcaughtEq : caught = sourceException := by
    simpa using hcaught
  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
    hparameters, hbind, hcallee, hexception, hpayload, hcaughtEq,
    hhandlerValid, hhandler]

/-! The source rule above covers every destination, while the original
    compiler equation only exposed the no-destination specialization.  This
    equation keeps the destination's flattened return slots explicit so the
    caught-call proof can be used for assignment-producing calls as well. -/

/-! The destination-carrying equation splits by what `wrap_rt` does with
    the destination: the kept case keeps the flattened slots, and the
    degraded case (`wrap_rt` drops the shape, unknown or global
    destination) keeps only the handler, matching
    `pan_to_crepScript.sml:247-260`. -/

theorem compileProg_call_handler_destination_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (returnNames : List Nat)
    (exception : ExceptionId) (handlerVar : VarName)
    (exceptionCode : α) (handlerProgram : Prog α)
    (handlerNames : List Nat) (compiledArguments : List (CrepExp α))
    (hexception : lookupInfo exception context.exceptions =
      some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments)
    (hnames : callDestinationNames context kind name = some returnNames) :
    compileProg context
        (.call (some (some (kind, name),
          some (exception, handlerVar, handlerProgram))) function arguments) =
      .call (some (returnNames,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments := by
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hexception, hhandler, harguments, hnames]

theorem compileProg_call_handler_degraded_destination_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (exception : ExceptionId) (handlerVar : VarName)
    (exceptionCode : α) (handlerProgram : Prog α)
    (handlerNames : List Nat) (compiledArguments : List (CrepExp α))
    (hexception : lookupInfo exception context.exceptions =
      some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments)
    (hnames : callDestinationNames context kind name = none) :
    compileProg context
        (.call (some (some (kind, name),
          some (exception, handlerVar, handlerProgram))) function arguments) =
      .call (some ([],
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments := by
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hexception, hhandler, harguments, hnames]

/-! Stateful counterparts of the caught-handler call equations.  The
    compatibility evaluator above intentionally remains available for older
    callers; these lemmas preserve the caller's globals and callee memory in
    the global-aware evaluator. -/

theorem compile_full_call_handler_state_simulation
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
    (hcall : evalCrepFullCallState functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { caller with
          locals := initializeCrepLocals caller.locals
            (allocatedNames context returnShape) }
      (some (allocatedNames context returnShape,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments =
      some result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress
      (fuel + 1 + (allocatedNames context returnShape).length) caller
      (compileProg context
        (.call (some (none, some (exception, handlerVar, handlerProgram)))
          function arguments)) =
      some (restoreCrepResultList caller.locals
        (allocatedNames context returnShape) result) := by
  rw [compileProg_call_handler_of_compiled context function arguments returnShape
    exception handlerVar exceptionCode handlerProgram handlerNames
    compiledArguments hfunction hexception hhandler harguments]
  have hbody :
      evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1)
      { caller with
          locals := initializeCrepLocals caller.locals
            (allocatedNames context returnShape) }
      (.call (some (allocatedNames context returnShape,
          some (exceptionCode,
            .seq (assignRet context.bytesInWord handlerNames)
              (compileProg context handlerProgram))))
        function compiledArguments) = some result := by
    simpa [evalCrepFullProgState] using hcall
  exact evalCrepFullProgState_nestedDecs_const_zero functions primitive ffi
    sharedMem baseAddress topAddress (fuel + 1) caller
    (allocatedNames context returnShape)
    (.call (some (allocatedNames context returnShape,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram))))
      function compiledArguments) result hbody

theorem compile_full_call_handler_state_destination_simulation
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
    (kind : VarKind) (name : VarName)
    (returnNames : List Nat)
    (exception handlerVar : VarName)
    (exceptionCode : α) (handlerProgram : Prog α)
    (handlerNames : List Nat) (result : CrepControlResult α)
    (hexception : lookupInfo exception context.exceptions = some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments)
    (hnames : callDestinationNames context kind name = some returnNames)
    (hcall : evalCrepFullCallState functions primitive ffi sharedMem
      baseAddress topAddress fuel caller
      (some (returnNames,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments =
      some result) :
    evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (compileProg context
        (.call (some (some (kind, name),
          some (exception, handlerVar, handlerProgram))) function arguments)) =
      some result := by
  rw [compileProg_call_handler_destination_of_compiled context function arguments
    kind name returnNames exception handlerVar exceptionCode handlerProgram
    handlerNames compiledArguments hexception hhandler harguments hnames]
  simpa [evalCrepFullProgState] using hcall
end Flapjack
