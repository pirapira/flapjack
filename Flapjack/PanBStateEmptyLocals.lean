import Flapjack.PanBst

/-!
# Pancake interaction-tree `empty_locals_def`

Source reference: `cakeml/pancake/semantics/pan_itreeSemScript.sml:32-34`.

The `bstate` operation clears only the local finite map.  All other
interaction-tree state components remain unchanged.
-/

namespace Flapjack

def panBEmptyLocals (state : PanBState α) : PanBState α :=
  { state with locals := fun _ => none }

@[simp] theorem panBEmptyLocals_locals (state : PanBState α) :
    (panBEmptyLocals state).locals = (fun _ => none) := by rfl

@[simp] theorem panBEmptyLocals_globals (state : PanBState α) :
    (panBEmptyLocals state).globals = state.globals := by rfl

@[simp] theorem panBEmptyLocals_memory (state : PanBState α) :
    (panBEmptyLocals state).memory = state.memory := by rfl

@[simp] theorem panBEmptyLocals_baseAddress (state : PanBState α) :
    (panBEmptyLocals state).baseAddress = state.baseAddress := by rfl

@[simp] theorem panBEmptyLocals_topAddress (state : PanBState α) :
    (panBEmptyLocals state).topAddress = state.topAddress := by rfl

end Flapjack
