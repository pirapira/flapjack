import Flapjack.PanValues

/-!
# Pancake `set_global`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:46-50`.
The source updates only the `globals` field of a bstate.  This projection is
represented directly as a name-to-value map update, leaving all sibling
bindings unchanged and inserting or replacing the selected global.
-/

namespace Flapjack

def panSetGlobal
    (globals : String → Option (PanValue α))
    (name : String) (value : PanValue α) : String → Option (PanValue α) :=
  updatePanValueMap globals name value

@[simp] theorem panSetGlobal_hit
    (globals : String → Option (PanValue α))
    (name : String) (value : PanValue α) :
    panSetGlobal globals name value name = some value := by
  simp [panSetGlobal, updatePanValueMap]

@[simp] theorem panSetGlobal_other
    (globals : String → Option (PanValue α))
    (name other : String) (value : PanValue α)
    (h : other ≠ name) :
    panSetGlobal globals name value other = globals other := by
  simp [panSetGlobal, updatePanValueMap, h]

end Flapjack
