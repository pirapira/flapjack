import Flapjack.PanValues

/-!
# Pancake `h_prog_dec`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:226-238`.

The source event for `h_prog_dec` is a program event, rather than an FFI
event.  It is therefore represented by the small source-shaped tree below
instead of being encoded as a `PanFfiTree`.  The tree keeps the program and
the extended source state visible at the event boundary.  A response carries
the subprogram result and post-state; the continuation restores the saved
local binding exactly as `res_var_def` does in Pancake.
-/

namespace Flapjack

inductive PanHProgDecOutcome where
  | normal
  | error
  deriving DecidableEq, Repr

inductive PanHProgDecResponse (α : Type u) (σ : Type v) where
  | failed
  | returned (outcome : PanHProgDecOutcome) (sourceState : σ)
  deriving Repr

inductive PanHProgDecTree (α : Type u) (σ : Type v) where
  | ret (outcome : PanHProgDecOutcome) (sourceState : σ)
  | vis (program : Prog α) (sourceState : σ)
      (k : PanHProgDecResponse α σ → PanHProgDecTree α σ)

structure PanHProgDecContext (α : Type u) (σ : Type v) where
  eval : σ → Exp α → Option (PanValue α)
  localValue : σ → VarName → Option (PanValue α)
  extendLocal : σ → VarName → PanValue α → σ
  restoreLocal : σ → VarName → Option (PanValue α) → σ

def panHProgDec (structs : StructContext)
    (context : PanHProgDecContext α σ)
    (sourceState : σ) (name : VarName) (shape : Shape)
    (value : Exp α) (body : Prog α) : PanHProgDecTree α σ :=
  match context.eval sourceState value with
  | some evaluatedValue =>
      if panShapeMatches (panValueShape structs evaluatedValue) shape then
        let oldValue := context.localValue sourceState name
        let extendedState := context.extendLocal sourceState name evaluatedValue
        .vis body extendedState (fun response =>
          match response with
          | .failed => .ret .error sourceState
          | .returned outcome bodyState =>
              let restoredState := context.restoreLocal bodyState name oldValue
              .ret outcome restoredState)
      else
        .ret .error sourceState
  | none => .ret .error sourceState

@[simp] theorem panHProgDec_invalid (structs : StructContext)
    (context : PanHProgDecContext α σ)
    (sourceState : σ) (name : VarName) (shape : Shape)
    (body : Prog α)
    (hmissing : context.eval sourceState (Exp.var .local "missing") = none) :
    panHProgDec structs context sourceState name shape
        (Exp.var .local "missing") body =
      PanHProgDecTree.ret .error sourceState := by
  simp [panHProgDec, hmissing]

theorem panHProgDec_response_failed (structs : StructContext)
    (context : PanHProgDecContext α σ)
    (sourceState : σ) (name : VarName) (shape : Shape)
    (value : Exp α) (body : Prog α)
    (evaluatedValue : PanValue α)
    (heval : context.eval sourceState value = some evaluatedValue)
    (hshape : panShapeMatches (panValueShape structs evaluatedValue) shape = true) :
    panHProgDec structs context sourceState name shape value body =
      .vis body (context.extendLocal sourceState name evaluatedValue) (fun response =>
        match response with
        | .failed => .ret .error sourceState
        | .returned outcome bodyState =>
            .ret outcome (context.restoreLocal bodyState name
              (context.localValue sourceState name))) := by
  simp [panHProgDec, heval, hshape]

end Flapjack
