import Flapjack.PanBst

/-!
# Pancake `empty_locals_def`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:436`.

The operation clears only the local-variable map of a `panSem.state`.
Globals, structure/code environments, memory, clock, endianness, FFI state,
and address metadata are preserved by the record update.
-/

namespace Flapjack

def panEmptyLocals (state : PanSemState α ffi) : PanSemState α ffi :=
  { state with locals := fun _ => none }

@[simp] theorem panEmptyLocals_locals (state : PanSemState α ffi) :
    (panEmptyLocals state).locals = (fun _ => none) := by rfl

@[simp] theorem panEmptyLocals_globals (state : PanSemState α ffi) :
    (panEmptyLocals state).globals = state.globals := by rfl

@[simp] theorem panEmptyLocals_memory (state : PanSemState α ffi) :
    (panEmptyLocals state).memory = state.memory := by rfl

@[simp] theorem panEmptyLocals_clock (state : PanSemState α ffi) :
    (panEmptyLocals state).clock = state.clock := by rfl

end Flapjack
