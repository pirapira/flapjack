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

theorem compileProg_call_handler_destination_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α))
    (destination : Option (VarKind × VarName))
    (returnNames : List Nat) (returnShape : Shape)
    (exception : ExceptionId) (handlerVar : VarName)
    (exceptionCode : α) (handlerProgram : Prog α)
    (handlerNames : List Nat) (compiledArguments : List (CrepExp α))
    (hfunction : lookupInfo function context.functions =
      some ([], returnShape))
    (hexception : lookupInfo exception context.exceptions =
      some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments)
    (hreturnNames :
      (match destination with
       | none => functionReturnNames context function
       | some (kind, name) =>
           match kind with
           | .local =>
               match lookupInfo name context.vars with
               | some (_, names) => names
               | none => []
           | .global => []) = returnNames) :
    compileProg context
        (.call (some (destination,
          some (exception, handlerVar, handlerProgram))) function arguments) =
      .call (some (returnNames,
        some (exceptionCode,
          .seq (assignRet context.bytesInWord handlerNames)
            (compileProg context handlerProgram)))) function compiledArguments := by
  have hfunctionReturnNames : functionReturnNames context function =
      allocatedNames context returnShape := by
    simp [functionReturnNames, hfunction]
  rw [hfunctionReturnNames] at hreturnNames
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hfunction, hexception, hhandler, harguments,
    functionReturnNames, allocatedNames] <;>
    exact hreturnNames

end Flapjack
