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
      (some (none, some (caught, handlerVariable, handlerProgram))) function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some sourceResult := by
  have hcaughtEq : caught = sourceException := by
    simpa using hcaught
  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
    hparameters, hbind, hcallee, hexception, hpayload, hcaughtEq,
    hhandlerValid, hhandler]

end Flapjack
