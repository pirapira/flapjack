import Flapjack.CrepeCallRaisedInversion

/-!
Inversion for a returned Crep call without a destination or handler.

This is the ordinary-call counterpart of destination-aware normal-call
inversion: a callee return is propagated as a caller return, together with
the callee's flattened result and memory.
-/

namespace Flapjack

theorem evalCrepFullCall_none_returned_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (arguments : List (CrepExp α))
    (target : CrepState α) (targetValues : List α)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller none function arguments =
      some (.returned target targetValues)) :
    ∃ values parameters body calleeLocals callee,
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress arguments = some values ∧
      lookupCompiledFunction function functions = some (parameters, body) ∧
      assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
      evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress fuel
        { locals := calleeLocals, memory := caller.memory } body =
          some (.returned callee targetValues) ∧
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
                      | returned callee calleeValues =>
                          have hsome :
                              some (CrepControlResult.returned
                                { caller with memory := callee.memory } calleeValues) =
                                some (CrepControlResult.returned target targetValues) := by
                            simpa [evalCrepFullCall, hvalues, hlookup, hassign, hcallee]
                              using hcall
                          have hresult := Option.some.inj hsome
                          have htargetValues : calleeValues = targetValues := by
                            injection hresult with _ htargetValues
                          cases htargetValues
                          refine ⟨values, parameters, body, calleeLocals, callee,
                            ?_, ?_, ?_, ?_, ?_⟩
                          · rfl
                          · rfl
                          · exact hassign
                          · exact hcallee
                          · have htarget :
                                some ({ caller with memory := callee.memory }) =
                                  some target := by
                              simpa [evalCrepFullCall, hvalues, hlookup, hassign, hcallee]
                                using hcall
                            exact (Option.some.inj htarget).symm
                      | normal callee
                      | raised callee exception
                      | broke callee label
                      | continued callee label
                      | finalFfi callee event =>
                          simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall

end Flapjack
