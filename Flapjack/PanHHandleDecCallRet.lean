import Flapjack.PanHHandleCallRet

/-!
# Pancake h_handle_deccall_ret

Source reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:388-401.

This source-shaped boundary handles the return from a declaration call.  It
checks both the declaration result shape and the callee result shape, installs
the result variable before emitting the declaration body event, and restores
the caller's previous result-variable binding after that body returns.
-/

namespace Flapjack

structure PanHHandleDecCallContext (α : Type u) (σ : Type v) where
  locals : σ → VarName → Option (PanValue α)
  setLocals : σ → (VarName → Option (PanValue α)) → σ
  emptyLocals : σ → σ
  setLocal : σ → VarName → PanValue α → σ
  restoreLocal : σ → VarName → Option (PanValue α) → σ

def panHHandleDecCallRet [BEq String]
    (context : PanHHandleDecCallContext α σ)
    (resultVariable : VarName) (declarationShape : Shape)
    (body : Prog α) (returnShape : Shape) (callerState : σ) :
    PanCallResponse α σ → PanCallTree α σ
  | .failed => .ret .error callerState
  | .returned .normal calleeState => .ret .error calleeState
  | .returned .broke calleeState => .ret .error calleeState
  | .returned .continued calleeState => .ret .error calleeState
  | .returned .error calleeState => .ret .error calleeState
  | .returned (.returned value) calleeState =>
      if panShapeMatches (panValueShape [] value) declarationShape &&
          panShapeMatches (panValueShape [] value) returnShape then
        let bodyState :=
          context.setLocal (context.setLocals calleeState (context.locals callerState))
            resultVariable value
        .vis body bodyState (fun response =>
          match response with
          | .failed => .ret .error calleeState
          | .returned outcome sourceState =>
              .ret outcome (context.restoreLocal sourceState resultVariable
                (context.locals callerState resultVariable)))
      else
        .ret .error calleeState
  | .returned (.raised exception value) calleeState =>
      .ret (.raised exception value) (context.emptyLocals calleeState)

@[simp] theorem panHHandleDecCallRet_failed [BEq String]
    (context : PanHHandleDecCallContext α σ)
    (resultVariable : VarName) (declarationShape : Shape)
    (body : Prog α) (returnShape : Shape) (callerState : σ) :
    panHHandleDecCallRet context resultVariable declarationShape body returnShape
        callerState .failed = .ret .error callerState := by
  rfl

end Flapjack
