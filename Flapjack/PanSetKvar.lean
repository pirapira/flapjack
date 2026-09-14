import Flapjack.PanValues

/-!
# Pancake `set_kvar`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:53-58`.
The helper dispatches to `set_var` for `Local` and `set_global` for `Global`;
the opposite environment is preserved in each branch.
-/

namespace Flapjack

structure PanKvarState (α : Type u) where
  locals : String → Option (PanValue α)
  globals : String → Option (PanValue α)

def panSetKvar
    (state : PanKvarState α) (kind : VarKind) (name : String)
    (value : PanValue α) : PanKvarState α :=
  match kind with
  | .local => { state with locals := updatePanValueMap state.locals name value }
  | .global => { state with globals := updatePanValueMap state.globals name value }

@[simp] theorem panSetKvar_local_globals
    (state : PanKvarState α) (name : String) (value : PanValue α) :
    (panSetKvar state .local name value).globals = state.globals := by
  rfl

@[simp] theorem panSetKvar_global_locals
    (state : PanKvarState α) (name : String) (value : PanValue α) :
    (panSetKvar state .global name value).locals = state.locals := by
  rfl

end Flapjack
