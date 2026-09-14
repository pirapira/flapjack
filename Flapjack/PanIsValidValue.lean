import Flapjack.PanLookupKvar

/-!
# Pancake `is_valid_value`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:67-74`.
The value is valid exactly when the selected local/global binding exists and
has the same source shape.
-/

namespace Flapjack

def panIsValidValue
    (structs : StructContext) (state : PanKvarState α) (kind : VarKind)
    (name : String) (value : PanValue α) : Bool :=
  match panLookupKvar state kind name with
  | some oldValue =>
      panShapeMatches (panValueShape structs value)
        (panValueShape structs oldValue)
  | none => false

@[simp] theorem panIsValidValue_missing
    (structs : StructContext) (state : PanKvarState α)
    (kind : VarKind) (name : String) (value : PanValue α)
    (h : panLookupKvar state kind name = none) :
    panIsValidValue structs state kind name value = false := by
  simp [panIsValidValue, h]

end Flapjack
