import Flapjack.CrepeCalleeStateExtensionCorrectness

/-!
Inversion lemmas for raised function calls.

These expose the callee-body witnesses hidden by the source and target call
evaluators when an uncaught exception is propagated to the caller.
-/

namespace Flapjack

theorem evalPanValueCall_raised_inversion
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
    (function : FunName) (arguments : List (Exp α))
    (returnedGlobals : VarName → Option (PanValue α))
    (returnedMemory : α → Option (PanValue α))
    (exception : ExceptionId) (value : PanValue α)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi
      primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory none function arguments =
      some (.raised (fun _ => none) returnedGlobals returnedMemory exception value)) :
    ∃ argumentValues parameters body calleeLocals bodyLocals,
      evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
        baseAddress topAddress bytesInWord arguments = some argumentValues ∧
      lookupPanFunction function functions = some (parameters, body) ∧
      panValueParametersValid structs none function argumentValues = true ∧
      bindPanValueParameters parameters argumentValues = some calleeLocals ∧
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive handler structs functions
        baseAddress topAddress bytesInWord fuel
        calleeLocals sourceGlobals sourceMemory body =
          some (.raised bodyLocals returnedGlobals returnedMemory exception value) ∧
      panValueExceptionValid structs none exception value = true ∧
      panValuePayloadWithinLimit structs value = true := by
  cases hvalues : evalPanValueExps structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord arguments with
  | none =>
      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at hcall
  | some argumentValues =>
      cases hlookup : lookupPanFunction function functions with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup] at hcall
      | some functionInfo =>
          cases functionInfo with
          | mk parameters body =>
              cases hparameters : panValueParametersValid structs none function
                  argumentValues with
              | false =>
                  simp [panValueParametersValid_none] at hparameters
              | true =>
                  cases hbind : bindPanValueParameters parameters argumentValues with
                  | none =>
                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
                        hbind] at hcall
                  | some calleeLocals =>
                      cases hbody : evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                          structs functions baseAddress topAddress bytesInWord fuel
                          calleeLocals sourceGlobals sourceMemory body with
                      | none =>
                          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues, hlookup,
                            hbind, hbody] at hcall
                      | some bodyResult =>
                          cases bodyResult with
                          | normal bodyLocals bodyGlobals bodyMemory
                          | returned bodyLocals bodyGlobals bodyMemory bodyValues
                          | broke bodyLocals bodyGlobals bodyMemory
                          | continued bodyLocals bodyGlobals bodyMemory =>
                              simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                hlookup, hbind, hbody] at hcall
                          | raised bodyLocals bodyGlobals bodyMemory bodyException bodyValue =>
                              cases hexception : panValueExceptionValid structs none
                                  bodyException bodyValue with
                              | false =>
                                  simp [panValueExceptionValid_none] at hexception
                              | true =>
                                  cases hlimit : panValuePayloadWithinLimit structs bodyValue with
                                  | false =>
                                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                        hlookup, hbind, hbody, hlimit]
                                        at hcall
                                  | true =>
                                      have hraised :
                                          PanValueControlResult.raised (fun _ => none)
                                              bodyGlobals bodyMemory bodyException bodyValue =
                                            PanValueControlResult.raised (fun _ => none)
                                              returnedGlobals returnedMemory exception value := by
                                        have hsome :
                                            some (PanValueControlResult.raised (fun _ => none)
                                              bodyGlobals bodyMemory bodyException bodyValue) =
                                              some (PanValueControlResult.raised (fun _ => none)
                                                returnedGlobals returnedMemory exception value) := by
                                          simpa [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                                            hlookup, hbind, hbody, hlimit]
                                            using hcall
                                        exact Option.some.inj hsome
                                      cases hraised
                                      refine ⟨argumentValues, parameters, body, calleeLocals,
                                        bodyLocals, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                      · rfl
                                      · rfl
                                      · exact hparameters
                                      · exact hbind
                                      · exact hbody
                                      · exact hexception
                                      · exact hlimit

theorem evalCrepFullCall_raised_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (destinations : List Nat)
    (function : FunName) (arguments : List (CrepExp α))
    (exception : α) (target : CrepState α)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (some (destinations, none)) function arguments =
      some (.raised target exception)) :
    ∃ values parameters body calleeLocals callee,
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress arguments = some values ∧
      lookupCompiledFunction function functions = some (parameters, body) ∧
      assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
      evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress fuel
        { locals := calleeLocals, memory := caller.memory } body =
          some (.raised callee exception) ∧
      target = { caller with memory := callee.memory } := by
  cases hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments with
  | none =>
      simp [evalCrepFullCall, hvalues] at hcall
  | some values =>
      cases hlookup : lookupCompiledFunction function functions with
      | none =>
          simp [evalCrepFullCall, hvalues, hlookup] at hcall
      | some functionInfo =>
          cases functionInfo with
          | mk parameters body =>
              cases hassign : assignCrepValues (fun _ => none) parameters values with
              | none =>
                  simp [evalCrepFullCall, hvalues, hlookup, hassign] at hcall
              | some calleeLocals =>
                  cases hcallee : evalCrepFullProg functions primitive ffi sharedMem
                      baseAddress topAddress fuel
                      { locals := calleeLocals, memory := caller.memory } body with
                  | none =>
                      simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall
                  | some calleeResult =>
                      cases calleeResult with
                      | raised calleeState calleeException =>
                          have hexception : calleeException = exception := by
                            have hsome :
                                some (CrepControlResult.raised
                                  { caller with memory := calleeState.memory }
                                  calleeException) =
                                  some (CrepControlResult.raised target exception) := by
                              simpa [evalCrepFullCall, hvalues, hlookup, hassign, hcallee]
                                using hcall
                            have hresult := Option.some.inj hsome
                            injection hresult with _ hexception
                          cases hexception
                          refine ⟨values, parameters, body, calleeLocals, calleeState,
                            ?_, ?_, ?_, ?_, ?_⟩
                          · rfl
                          · rfl
                          · exact hassign
                          · exact hcallee
                          · have htarget :
                                some ({ caller with memory := calleeState.memory }) =
                                  some target := by
                              simpa [evalCrepFullCall, hvalues, hlookup, hassign, hcallee]
                                using hcall
                            exact (Option.some.inj htarget).symm
                      | normal calleeState =>
                          simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall
                      | returned calleeState calleeValues =>
                          cases hdest : assignCrepValues caller.locals destinations calleeValues with
                          | none =>
                              simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee,
                                hdest] at hcall
                          | some callerLocals =>
                              simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee,
                                hdest] at hcall
                      | broke calleeState label
                      | continued calleeState label
                      | finalFfi calleeState event =>
                          simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall

end Flapjack
