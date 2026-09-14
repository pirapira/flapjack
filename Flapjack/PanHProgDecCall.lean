import Flapjack.PanHHandleDecCallRet

/-!
# Pancake h_prog_deccall

Source reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:404-411.

The declaration-call dispatcher evaluates all argument expressions before
performing code lookup.  On success it emits the callee program event and
installs the callee locals; the return handler is kept explicit so its result
and exception behavior remain the source boundary from h_handle_deccall_ret.
-/

namespace Flapjack

structure PanHProgDecCallContext (α : Type u) (σ : Type v) where
  evalArguments : σ → List (Exp α) → Option (List (PanValue α))
  lookupCode : σ → FunName → List (PanValue α) →
    Option (Prog α × (VarName → Option (PanValue α)) × Shape)
  setLocals : σ → (VarName → Option (PanValue α)) → σ
  handleReturn : PanHHandleDecCallContext α σ

def panHProgDecCall
    (context : PanHProgDecCallContext α σ)
    (resultVariable : VarName) (declarationShape : Shape)
    (function : FunName) (arguments : List (Exp α))
    (body : Prog α) (sourceState : σ) :
    PanCallTree α σ :=
  match context.evalArguments sourceState arguments with
  | some values =>
      match context.lookupCode sourceState function values with
      | some (callee, calleeLocals, returnShape) =>
          .vis callee (context.setLocals sourceState calleeLocals)
            (panHHandleDecCallRet context.handleReturn resultVariable
              declarationShape body returnShape sourceState)
      | none => .ret .error sourceState
  | none => .ret .error sourceState

@[simp] theorem panHProgDecCall_arguments_error
    (context : PanHProgDecCallContext α σ)
    (resultVariable : VarName) (declarationShape : Shape)
    (function : FunName) (arguments : List (Exp α))
    (body : Prog α) (sourceState : σ)
    (heval : context.evalArguments sourceState arguments = none) :
    panHProgDecCall context resultVariable declarationShape function arguments body sourceState =
      .ret .error sourceState := by
  simp [panHProgDecCall, heval]

end Flapjack
