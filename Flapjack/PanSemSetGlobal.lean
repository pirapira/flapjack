import Flapjack.PanSetKvar

/-!
# Pancake `panSem.set_global`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:403-405`.

The source updates only the global finite map and preserves the local map.
`PanKvarState` contains exactly those observable environments for this helper.
-/

namespace Flapjack

def panSemSetGlobal
    (state : PanKvarState α) (name : String) (value : PanValue α) : PanKvarState α :=
  { state with globals := updatePanValueMap state.globals name value }

@[simp] theorem panSemSetGlobal_locals
    (state : PanKvarState α) (name : String) (value : PanValue α) :
    (panSemSetGlobal state name value).locals = state.locals := by
  rfl

@[simp] theorem panSemSetGlobal_hit
    (state : PanKvarState α) (name : String) (value : PanValue α) :
    (panSemSetGlobal state name value).globals name = some value := by
  simp [panSemSetGlobal, updatePanValueMap]

end Flapjack
