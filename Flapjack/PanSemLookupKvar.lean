import Flapjack.PanSetKvar

/-!
# Pancake `panSem.lookup_kvar`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:415-421`.

The source dispatches to the local or global environment according to
`VarKind`.  `PanKvarState` contains the two maps involved in the projection.
-/

namespace Flapjack

def panSemLookupKvar
    (state : PanKvarState α) (kind : VarKind) (name : String) : Option (PanValue α) :=
  match kind with
  | .local => state.locals name
  | .global => state.globals name

@[simp] theorem panSemLookupKvar_local
    (state : PanKvarState α) (name : String) :
    panSemLookupKvar state .local name = state.locals name := by
  rfl

@[simp] theorem panSemLookupKvar_global
    (state : PanKvarState α) (name : String) :
    panSemLookupKvar state .global name = state.globals name := by
  rfl

end Flapjack
