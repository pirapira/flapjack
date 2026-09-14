import Flapjack.PanSemLookupKvar

/-!
# Pancake `panSem.is_valid_value`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:469-475`.

The source validates a value by looking up the selected local/global binding and
comparing its source shape.  A missing binding is invalid.
-/

namespace Flapjack

def panSemIsValidValue
    (structs : StructContext) (state : PanKvarState α) (kind : VarKind)
    (name : String) (value : PanValue α) : Bool :=
  match panSemLookupKvar state kind name with
  | some oldValue =>
      panShapeMatches (panValueShape structs value) (panValueShape structs oldValue)
  | none => false

@[simp] theorem panSemIsValidValue_missing
    (structs : StructContext) (state : PanKvarState α)
    (kind : VarKind) (name : String) (value : PanValue α)
    (h : panSemLookupKvar state kind name = none) :
    panSemIsValidValue structs state kind name value = false := by
  simp [panSemIsValidValue, h]

end Flapjack
