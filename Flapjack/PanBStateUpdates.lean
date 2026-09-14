import Flapjack.PanBst

/-!
# Pancake `set_var` on `bstate`

Source reference: `cakeml/pancake/semantics/pan_itreeSemScript.sml:39-42`.

The interaction-tree state update changes only `locals`; unlike the separate
`panSem` state update, this boundary has no clock or FFI fields to modify.
-/

namespace Flapjack

def panBSetVar (state : PanBState α) (name : VarName)
    (value : PanValue α) : PanBState α :=
  { state with locals := updatePanValueMap state.locals name value }

@[simp] theorem panBSetVar_locals (state : PanBState α)
    (name : VarName) (value : PanValue α) :
    (panBSetVar state name value).locals =
      updatePanValueMap state.locals name value := by rfl

@[simp] theorem panBSetVar_globals (state : PanBState α)
    (name : VarName) (value : PanValue α) :
    (panBSetVar state name value).globals = state.globals := by rfl

@[simp] theorem panBSetVar_memory (state : PanBState α)
    (name : VarName) (value : PanValue α) :
    (panBSetVar state name value).memory = state.memory := by rfl

end Flapjack
