import Flapjack.PanHHandleCallRet

/-!
# Pancake h_prog_call

Source reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:376-385.

The call dispatcher evaluates arguments before code lookup and emits the
callee program event only after both stages succeed.  The response continuation
is the source h_handle_call_ret boundary.
-/

namespace Flapjack

structure PanHProgCallContext (α : Type u) (σ : Type v) where
  evalArguments : σ → List (Exp α) → Option (List (PanValue α))
  lookupCode : σ → FunName → List (PanValue α) →
    Option (Prog α × (VarName → Option (PanValue α)) × Shape)
  setLocals : σ → (VarName → Option (PanValue α)) → σ
  handleReturn : PanHHandleCallContext α σ

def panHProgCall
    (context : PanHProgCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (sourceState : σ) :
    PanCallTree α σ :=
  match context.evalArguments sourceState arguments with
  | some values =>
      match context.lookupCode sourceState function values with
      | some (callee, calleeLocals, returnShape) =>
          .vis callee (context.setLocals sourceState calleeLocals)
            (panHHandleCallRet context.handleReturn callType returnShape sourceState)
      | none => .ret .error sourceState
  | none => .ret .error sourceState

@[simp] theorem panHProgCall_arguments_error
    (context : PanHProgCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (sourceState : σ)
    (heval : context.evalArguments sourceState arguments = none) :
    panHProgCall context callType function arguments sourceState =
      .ret .error sourceState := by
  simp [panHProgCall, heval]

end Flapjack
