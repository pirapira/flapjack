import Flapjack.PanHHandleCallRet

/-!
# Pancake `h_prog_call`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:377-385`.

The source dispatcher evaluates every argument before looking up the callee.
On a successful lookup it emits the callee program with the freshly built
locals and leaves return handling to `h_handle_call_ret`; either failed
evaluation or a missing/incompatible code entry returns `Error` immediately.
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
    (function : FunName) (arguments : List (Exp α)) (sourceState : σ) :
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
    (function : FunName) (arguments : List (Exp α)) (sourceState : σ)
    (heval : context.evalArguments sourceState arguments = none) :
    panHProgCall context callType function arguments sourceState =
      .ret .error sourceState := by
  simp [panHProgCall, heval]

theorem panHProgCall_lookup_error
    (context : PanHProgCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) (sourceState : σ)
    (values : List (PanValue α))
    (heval : context.evalArguments sourceState arguments = some values)
    (hlookup : context.lookupCode sourceState function values = none) :
    panHProgCall context callType function arguments sourceState =
      .ret .error sourceState := by
  simp [panHProgCall, heval, hlookup]

end Flapjack
