import Flapjack.CrepeCallStateExtension
import Flapjack.CrepeCallReturnedInversion

/-!
Inversion for a normal Crep call without a destination or handler.

With ordinary-call metadata, a normal result means that the callee body
finished normally; no caller-local assignment is performed.
-/

namespace Flapjack

/-!
Inversion for a normal destination-aware Crep call.

A normal destination call can arise either from a callee that itself finished
normally, or from a returned-value destination assignment.  Keeping these
cases separate makes the returned-value branch explicit in the
declaration-call correctness proof.
-/

theorem evalCrepFullCall_normal_inversion
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
    (target : CrepState α)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (some (destinations, none)) function arguments =
      some (.normal target)) :
    (∃ values parameters body calleeLocals callee,
       evalCrepFullExps caller.locals caller.memory
         baseAddress topAddress arguments = some values ∧
       lookupCompiledFunction function functions = some (parameters, body) ∧
       assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
       evalCrepFullProg functions primitive ffi sharedMem
         baseAddress topAddress fuel
         { locals := calleeLocals, memory := caller.memory } body =
           some (.normal callee) ∧
       target = { caller with memory := callee.memory })
    ∨
    (∃ values parameters body calleeLocals callee calleeValues callerLocals,
       evalCrepFullExps caller.locals caller.memory
         baseAddress topAddress arguments = some values ∧
       lookupCompiledFunction function functions = some (parameters, body) ∧
       assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
       evalCrepFullProg functions primitive ffi sharedMem
         baseAddress topAddress fuel
         { locals := calleeLocals, memory := caller.memory } body =
           some (.returned callee calleeValues) ∧
       assignCrepValues caller.locals destinations calleeValues =
         some callerLocals ∧
       target = { locals := callerLocals, memory := callee.memory }) := by
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
                      | normal callee =>
                          refine Or.inl ⟨values, parameters, body, calleeLocals, callee,
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
                      | returned callee calleeValues =>
                          cases hdest : assignCrepValues caller.locals destinations calleeValues with
                          | none =>
                              simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee,
                                hdest] at hcall
                          | some callerLocals =>
                              refine Or.inr ⟨values, parameters, body, calleeLocals, callee,
                                calleeValues, callerLocals, ?_, ?_, ?_, ?_, ?_, ?_⟩
                              · rfl
                              · rfl
                              · exact hassign
                              · exact hcallee
                              · exact hdest
                              · have htarget :
                                    some ({ locals := callerLocals, memory := callee.memory }) =
                                      some target := by
                                  simpa [evalCrepFullCall, hvalues, hlookup, hassign, hcallee,
                                    hdest] using hcall
                                exact (Option.some.inj htarget).symm
                      | raised callee exception
                      | broke callee label
                      | continued callee label
                      | finalFfi callee event =>
                          simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall

theorem evalCrepFullCall_none_normal_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (arguments : List (CrepExp α)) (target : CrepState α)
    (hcall : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller none function arguments =
      some (.normal target)) :
    ∃ values parameters body calleeLocals callee,
      evalCrepFullExps caller.locals caller.memory
        baseAddress topAddress arguments = some values ∧
      lookupCompiledFunction function functions = some (parameters, body) ∧
      assignCrepValues (fun _ => none) parameters values = some calleeLocals ∧
      evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress fuel
        { locals := calleeLocals, memory := caller.memory } body =
          some (.normal callee) ∧
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
                      | normal callee =>
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
                      | returned callee values
                      | raised callee exception
                      | broke callee label
                      | continued callee label
                      | finalFfi callee event =>
                          simp [evalCrepFullCall, hvalues, hlookup, hassign, hcallee] at hcall

end Flapjack
