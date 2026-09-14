import Flapjack.PanValues

/-!
# Pancake h_handle_call_ret

Source reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:340-374.

This is the source-shaped call-return boundary.  It is intentionally kept
separate from the fuel-bounded value evaluator: the HOL definition consumes a
program-event response and returns a program-event tree, while the evaluator
also has to account for fuel and expression lookup.  Keeping the response
boundary explicit makes the caller-local restoration and exception-handler
transition observable and prevents the two semantics from being conflated.
-/

namespace Flapjack

inductive PanCallOutcome (α : Type u) where
  | normal
  | returned (value : PanValue α)
  | raised (exception : ExceptionId) (value : PanValue α)
  | broke
  | continued
  | error
  deriving Repr

inductive PanCallResponse (α : Type u) (σ : Type v) where
  | failed
  | returned (outcome : PanCallOutcome α) (sourceState : σ)
  deriving Repr

inductive PanCallTree (α : Type u) (σ : Type v) where
  | ret (outcome : PanCallOutcome α) (sourceState : σ)
  | vis (program : Prog α) (sourceState : σ)
      (k : PanCallResponse α σ → PanCallTree α σ)

structure PanHHandleCallContext (α : Type u) (σ : Type v) where
  /-- The complete caller local environment saved across the callee call. -/
  locals : σ → VarName → Option (PanValue α)
  setLocals : σ → (VarName → Option (PanValue α)) → σ
  emptyLocals : σ → σ
  setKvar : σ → VarKind → VarName → PanValue α → σ
  isValidValue : σ → VarKind → VarName → PanValue α → Bool
  exceptionShape : σ → ExceptionId → Option Shape

def panCallHandlerContinuation (calleeState : σ) :
    PanCallResponse α σ → PanCallTree α σ
  | .failed => .ret .error calleeState
  | .returned outcome sourceState => .ret outcome sourceState

def panHHandleCallRet [BEq String]
    (context : PanHHandleCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (returnShape : Shape) (callerState : σ) :
    PanCallResponse α σ → PanCallTree α σ
  | .failed => .ret .error callerState
  | .returned .normal calleeState => .ret .error calleeState
  | .returned .broke calleeState => .ret .error calleeState
  | .returned .continued calleeState => .ret .error calleeState
  | .returned .error calleeState => .ret .error calleeState
  | .returned (.returned value) calleeState =>
      if panShapeMatches (panValueShape [] value) returnShape then
        match callType with
        | none => .ret (.returned value) (context.emptyLocals calleeState)
        | some (none, _) =>
            .ret .normal (context.setLocals calleeState (context.locals callerState))
        | some (some (kind, name), _) =>
            if context.isValidValue callerState kind name value then
              .ret .normal (context.setKvar calleeState kind name value)
            else
              .ret .error calleeState
      else
        .ret .error calleeState
  | .returned (.raised exception value) calleeState =>
      match callType with
      | none => .ret (.raised exception value) (context.emptyLocals calleeState)
      | some (_, none) =>
          .ret (.raised exception value) (context.emptyLocals calleeState)
      | some (_, some (caught, handlerVariable, handler)) =>
          if exception == caught then
            match context.exceptionShape callerState exception with
            | some shape =>
                if panShapeMatches (panValueShape [] value) shape &&
                    context.isValidValue callerState .local handlerVariable value then
                  let handlerState :=
                    context.setLocals calleeState
                      (updatePanValueMap (context.locals callerState) handlerVariable value)
                  .vis handler handlerState
                    (panCallHandlerContinuation calleeState)
                else
                  .ret .error calleeState
            | none => .ret .error calleeState
          else
            .ret (.raised exception value) (context.emptyLocals calleeState)

@[simp] theorem panHHandleCallRet_failed [BEq String]
    (context : PanHHandleCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (returnShape : Shape) (callerState : σ) :
    panHHandleCallRet context callType returnShape callerState .failed =
      .ret .error callerState := by
  rfl

theorem panHHandleCallRet_return_shape_error [BEq String]
    (context : PanHHandleCallContext α σ)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (returnShape : Shape) (callerState calleeState : σ)
    (value : PanValue α)
    (hshape : panShapeMatches (panValueShape [] value) returnShape = false) :
    panHHandleCallRet context callType returnShape callerState
        (.returned (.returned value) calleeState) = .ret .error calleeState := by
  simp [panHHandleCallRet, hshape]

end Flapjack
