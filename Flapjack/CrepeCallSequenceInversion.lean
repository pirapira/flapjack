import Flapjack.CrepeZeroDeclarationInversion

/-!
Inversion for the call/continuation sequence emitted by declaration calls.

The first call may terminate with any Crep control result.  A normal call
continues into the body; every other result short-circuits the sequence.
Keeping both branches explicit lets the declaration correctness proof handle
normal returns and raised control flow without unfolding the evaluator again.
-/

namespace Flapjack

theorem evalCrepFullProg_call_seq_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α)
    (info : Option (List Nat × Option (α × CrepProg α)))
    (function : FunName) (arguments : List (CrepExp α))
    (body : CrepProg α) (result : CrepControlResult α)
    (heval : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (.seq (.call info function arguments) body) = some result) :
    ∃ callResult,
      evalCrepFullCall functions primitive ffi sharedMem
        baseAddress topAddress fuel state info function arguments =
        some callResult ∧
      match callResult with
      | .normal callState =>
          evalCrepFullProg functions primitive ffi sharedMem
            baseAddress topAddress (fuel + 1) callState body = some result
      | other => result = other := by
  cases hcallResult : evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress fuel state info function arguments with
  | none =>
      simp [evalCrepFullProg, hcallResult] at heval
  | some callResult =>
      refine ⟨callResult, rfl, ?_⟩
      cases callResult with
      | normal callState =>
          simpa [evalCrepFullProg, hcallResult] using heval
      | returned callState values =>
          have hresult :
              some (.returned callState values) = some result := by
            simpa [evalCrepFullProg, hcallResult] using heval
          exact (Option.some.inj hresult).symm
      | raised callState exception =>
          have hresult :
              some (.raised callState exception) = some result := by
            simpa [evalCrepFullProg, hcallResult] using heval
          exact (Option.some.inj hresult).symm
      | broke callState label =>
          have hresult :
              some (.broke callState label) = some result := by
            simpa [evalCrepFullProg, hcallResult] using heval
          exact (Option.some.inj hresult).symm
      | continued callState label =>
          have hresult :
              some (.continued callState label) = some result := by
            simpa [evalCrepFullProg, hcallResult] using heval
          exact (Option.some.inj hresult).symm
      | finalFfi callState event =>
          have hresult :
              some (.finalFfi callState event) = some result := by
            simpa [evalCrepFullProg, hcallResult] using heval
          exact (Option.some.inj hresult).symm

end Flapjack
