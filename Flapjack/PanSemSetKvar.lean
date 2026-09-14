import Flapjack.PanSetKvar

/-!
# Pancake `panSem.set_kvar`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:408-414`.

The source dispatches to local or global map update according to `VarKind`.
The existing `PanKvarState` captures exactly the two projections touched by
this helper.
-/

namespace Flapjack

def panSemSetKvar
    (state : PanKvarState α) (kind : VarKind) (name : String)
    (value : PanValue α) : PanKvarState α :=
  panSetKvar state kind name value

@[simp] theorem panSemSetKvar_eq_panSetKvar
    (state : PanKvarState α) (kind : VarKind) (name : String)
    (value : PanValue α) :
    panSemSetKvar state kind name value = panSetKvar state kind name value := by
  rfl

end Flapjack
