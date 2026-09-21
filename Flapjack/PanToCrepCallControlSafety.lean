import Flapjack.PanToCrepCorrectnessBoundary

/-!
Control-safety for the source-to-Crep `call` constructor.  A source or Crep
call can only propagate a loop-control result (`broke`/`continued`) out of an
exception handler: the callee's own `broke`/`continued` results are discarded
(`none`) by both evaluators.  Hence a call whose metadata carries no handler
can never expose a nonzero loop label at the boundary.  This is the no-handler
sublemma requested for the arbitrary `pc_compile_correct` closure; it does not
assert unconditional call safety.
-/

namespace Flapjack

theorem evalPanValueCallWithPrimitiveCallsAndFfi_no_handler_not_broke_continued
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (result : PanValueControlResult α)
    (hnoHandler : ∀ destination caughtHandler,
      info = some (destination, some caughtHandler) → False)
    (h : evalPanValueCallWithPrimitiveCallsAndFfi primitive handler structs
      functions baseAddress topAddress bytesInWord fuel locals globals memory
      info function arguments = some result) :
    (∀ l g m, result ≠ .broke l g m) ∧
      (∀ l g m, result ≠ .continued l g m) := by
  cases fuel with
  | zero => simp [evalPanValueCallWithPrimitiveCallsAndFfi] at h
  | succ fuel =>
      cases hvalues : evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments with
      | none =>
          simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues] at h
      | some values =>
          cases hlookup : lookupPanFunction function functions with
          | none =>
              simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                hlookup] at h
          | some entry =>
              obtain ⟨parameters, body⟩ := entry
              cases hbind : bindPanValueParameters parameters values with
              | none =>
                  simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                    hlookup, hbind] at h
              | some calleeLocals =>
                  cases hbody : evalPanValueProgWithPrimitiveCallsAndFfi
                      primitive handler structs functions baseAddress
                      topAddress bytesInWord fuel calleeLocals globals memory
                      body with
                  | none =>
                      simp [evalPanValueCallWithPrimitiveCallsAndFfi, hvalues,
                        hlookup, hbind, hbody] at h
                  | some bodyResult =>
                      simp only [evalPanValueCallWithPrimitiveCallsAndFfi] at h
                      cases bodyResult with
                      | normal bodyLocals bodyGlobals bodyMemory =>
                          simp_all
                      | returned bodyLocals bodyGlobals bodyMemory bodyValues =>
                          cases hwithin : panValueValuesWithinLimit structs bodyValues with
                          | false => simp_all
                          | true =>
                              cases info with
                              | none =>
                                  simp_all
                                  rw [← h]
                                  exact ⟨(fun l g m => by simp),
                                    (fun l g m => by simp)⟩
                              | some destination =>
                                  obtain ⟨destinationValue, _handlerOption⟩ :=
                                    destination
                                  cases hassign : assignPanValueCallResult
                                      locals bodyGlobals destinationValue
                                      bodyValues (structs := structs) with
                                  | none => simp_all
                                  | some assigned =>
                                      obtain ⟨assignedLocals, assignedGlobals⟩ :=
                                        assigned
                                      simp_all
                                      rw [← h]
                                      exact ⟨(fun l g m => by simp),
                                        (fun l g m => by simp)⟩
                      | raised bodyLocals bodyGlobals bodyMemory exception value =>
                          cases hpayload : panValuePayloadWithinLimit structs value with
                          | false => simp_all
                          | true =>
                              cases info with
                              | none =>
                                  simp_all
                                  rw [← h]
                                  exact ⟨(fun l g m => by simp),
                                    (fun l g m => by simp)⟩
                              | some destination =>
                                  obtain ⟨destinationValue, handlerOption⟩ :=
                                    destination
                                  cases handlerOption with
                                  | none =>
                                      simp_all
                                      rw [← h]
                                      exact ⟨(fun l g m => by simp),
                                        (fun l g m => by simp)⟩
                                  | some caughtHandler =>
                                      exact absurd rfl
                                        (hnoHandler destinationValue caughtHandler)
                      | broke bodyLocals bodyGlobals bodyMemory =>
                          simp_all
                      | continued bodyLocals bodyGlobals bodyMemory =>
                          simp_all

theorem panValueCrepProgramStateControlSafe_call_no_handler
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (name : FunName) (args : List (Exp α))
    (hnoHandler : ∀ destination caughtHandler,
      info = some (destination, some caughtHandler) → False) :
    PanValueCrepProgramStateControlSafe (.call info name args) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      have hcall :
          evalPanValueCallWithPrimitiveCallsAndFfi primitive sourceHandler structs
            sourceFunctions baseAddress topAddress bytesInWord sourceFuel
            sourceLocals sourceGlobals sourceMemory info name args =
            some sourceResult := by
        simpa [evalPanValueProgWithPrimitiveCallsAndFfi] using hsource
      obtain ⟨hnotBroke, hnotContinued⟩ :=
        evalPanValueCallWithPrimitiveCallsAndFfi_no_handler_not_broke_continued
          primitive sourceHandler structs sourceFunctions baseAddress topAddress
          bytesInWord sourceFuel sourceLocals sourceGlobals sourceMemory info name
          args sourceResult hnoHandler hcall
      cases sourceResult with
      | normal resultLocals resultGlobals resultMemory =>
          simp [panValuePcControlLabelSafe]
      | returned resultLocals resultGlobals resultMemory values =>
          simp [panValuePcControlLabelSafe]
      | raised resultLocals resultGlobals resultMemory exception value =>
          simp [panValuePcControlLabelSafe]
      | broke resultLocals resultGlobals resultMemory =>
          exact absurd rfl (hnotBroke resultLocals resultGlobals resultMemory)
      | continued resultLocals resultGlobals resultMemory =>
          exact absurd rfl (hnotContinued resultLocals resultGlobals resultMemory)

end Flapjack
