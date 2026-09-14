import Flapjack.PanSetKvar

/-!
# Pancake `lookup_kvar`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:60-64`.
The helper selects the local or global environment according to `VarKind` and
performs the corresponding source map lookup.
-/

namespace Flapjack

def panLookupKvar
    (state : PanKvarState α) (kind : VarKind) (name : String) :
    Option (PanValue α) :=
  match kind with
  | .local => state.locals name
  | .global => state.globals name

@[simp] theorem panLookupKvar_local
    (state : PanKvarState α) (name : String) :
    panLookupKvar state .local name = state.locals name := by
  rfl

@[simp] theorem panLookupKvar_global
    (state : PanKvarState α) (name : String) :
    panLookupKvar state .global name = state.globals name := by
  rfl

end Flapjack
