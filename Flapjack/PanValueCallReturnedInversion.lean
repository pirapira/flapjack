import Flapjack.PanValueDecCallInversion

/-!
Inversion for a successful source function call with no destination.

The declaration-call proof needs the callee-body evaluation hidden inside the
source call evaluator.  This theorem exposes that evaluation together with
the argument, parameter-binding, and result-validation witnesses.
-/

namespace Flapjack

theorem evalPanValueCall_returned_inversion
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
    (returnedGlobals : VarName → Option (PanValue α))
    (returnedMemory : α → Option (PanValue α))
    (returnedValues : List (PanValue α))
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.returned (fun _ => none) returnedGlobals returnedMemory returnedValues)) :
    ∃ argumentValues parameters body calleeLocals bodyLocals,
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess) = some argumentValues ∧
      lookupPanFunction function functions = some (parameters, body) ∧
      panValueParametersValid structs contracts function argumentValues = true ∧
      bindPanValueParameters parameters argumentValues = some calleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs functions
        baseAddress topAddress bytesInWord fuel
        calleeLocals sourceGlobals sourceMemory body
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
          some (.returned bodyLocals returnedGlobals returnedMemory returnedValues) ∧
      panValueReturnValid structs contracts function returnedValues = true ∧
      panValueValuesWithinLimit structs returnedValues = true := by
  cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess) with
  | none =>
      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at hcall
  | some argumentValues =>
      cases hlookup : lookupPanFunction function functions with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup] at hcall
      | some functionInfo =>
          cases functionInfo with
          | mk parameters body =>
              cases hparameters : panValueParametersValid structs contracts function
                  argumentValues with
              | false =>
                  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
                    hparameters] at hcall
              | true =>
                  cases hbind : bindPanValueParameters parameters argumentValues with
                  | none =>
                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
                        hparameters, hbind] at hcall
                  | some calleeLocals =>
                      cases hbody : evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                          structs functions baseAddress topAddress bytesInWord fuel
                          calleeLocals sourceGlobals sourceMemory body
                          (memoryAccess := memoryAccess) (contracts := contracts)
                          (memoryHandler := memoryHandler) with
                      | none =>
                          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
                            hparameters, hbind, hbody] at hcall
                      | some bodyResult =>
                          cases bodyResult with
                          | normal bodyLocals bodyGlobals bodyMemory =>
                              simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                hlookup, hparameters, hbind, hbody] at hcall
                          | returned bodyLocals bodyGlobals bodyMemory bodyValues =>
                              cases hreturn : panValueReturnValid structs contracts function
                                  bodyValues with
                              | false =>
                                  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                    hlookup, hparameters, hbind, hbody, hreturn] at hcall
                              | true =>
                                  cases hlimit : panValueValuesWithinLimit structs bodyValues with
                                  | false =>
                                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                        hlookup, hparameters, hbind, hbody, hreturn, hlimit] at hcall
                                  | true =>
                                      have hreturned :
                                          PanValueControlResult.returned (fun _ => none)
                                              bodyGlobals bodyMemory bodyValues =
                                            PanValueControlResult.returned (fun _ => none)
                                              returnedGlobals returnedMemory returnedValues := by
                                        have hsome :
                                            some (PanValueControlResult.returned (fun _ => none)
                                              bodyGlobals bodyMemory bodyValues) =
                                              some (PanValueControlResult.returned (fun _ => none)
                                                returnedGlobals returnedMemory returnedValues) := by
                                          simpa [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                            hlookup, hparameters, hbind, hbody, hreturn, hlimit]
                                            using hcall
                                        exact Option.some.inj hsome
                                      cases hreturned
                                      refine ⟨argumentValues, parameters, body, calleeLocals,
                                        bodyLocals, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                      · rfl
                                      · rfl
                                      · exact hparameters
                                      · exact hbind
                                      · exact hbody
                                      · exact hreturn
                                      · exact hlimit
                                      
                          | raised bodyLocals bodyGlobals bodyMemory exception value
                          | broke bodyLocals bodyGlobals bodyMemory
                          | continued bodyLocals bodyGlobals bodyMemory =>
                              simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                hlookup, hparameters, hbind, hbody] at hcall

end Flapjack
