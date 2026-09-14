import Flapjack.PanValues
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_assign`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:254-275`.

The expression evaluator, validity predicate, and kind-specific state update
are explicit callbacks.  This preserves the source boundary: a valid value
returns `NONE` with the updated state, while failed evaluation or validation
returns `Error` with the original state.
-/

namespace Flapjack

inductive PanHProgAssignResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  deriving Repr

def panHProgAssign [BEq α]
    (sourceState : σ)
    (eval : σ → Exp α → Option (PanValue α))
    (isValid : σ → VarKind → VarName → PanValue α → Bool)
    (setValue : σ → VarKind → VarName → PanValue α → σ)
    (kind : VarKind) (name : VarName) (expression : Exp α) :
    PanFfiTree (PanHProgAssignResult σ) :=
  match eval sourceState expression with
  | some value =>
      if isValid sourceState kind name value then
        .ret (.normal (setValue sourceState kind name value))
      else
        .ret (.error sourceState)
  | none => .ret (.error sourceState)

@[simp] theorem panHProgAssign_invalid [BEq α]
    (sourceState : σ)
    (eval : σ → Exp α → Option (PanValue α))
    (isValid : σ → VarKind → VarName → PanValue α → Bool)
    (setValue : σ → VarKind → VarName → PanValue α → σ)
    (kind : VarKind) (name : VarName)
    (heval : eval sourceState (Exp.var .local "missing") = none) :
    panHProgAssign sourceState eval isValid setValue kind name
        (Exp.var .local "missing") =
      PanFfiTree.ret (α := PanHProgAssignResult σ)
        (PanHProgAssignResult.error sourceState) := by
  simp [panHProgAssign, heval]

end Flapjack
