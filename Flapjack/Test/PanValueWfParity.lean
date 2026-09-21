import Flapjack.PanValues

namespace Flapjack.Test.PanValueWfParity

open Flapjack

/-! Direct parity for the ported Cake value-level well-formedness predicate
    `is_wf_shape_v` (`panPropsScript.sml:24`) and its shape bridge
    `is_wf_shape_of_v` (`:38`). -/

def namedContext : StructContext :=
  [("S", { fields := [], size := 1 })]

def wordValue : PanValue Nat := .word 3

def recordValue : PanValue Nat := .rStruct [.word 1, .word 2]

def namedValue : PanValue Nat := .nStruct "S" []

def unknownNamedValue : PanValue Nat := .nStruct "T" []

theorem panValueIsWf_word : panValueIsWf ([] : StructContext) wordValue = true := by
  simp [panValueIsWf, wordValue]

theorem panValueIsWf_record : panValueIsWf ([] : StructContext) recordValue = true := by
  simp [panValueIsWf, panValueIsWfValues, recordValue]

theorem panValueIsWf_named : panValueIsWf namedContext namedValue = true := by
  simp [panValueIsWf, panValueIsWfFields, namedContext, namedValue, lookupInfo]

def parityGuard : Bool :=
  panValueIsWf ([] : StructContext) wordValue &&
  panValueIsWf ([] : StructContext) recordValue &&
  panValueIsWf namedContext namedValue &&
  !panValueIsWf namedContext unknownNamedValue &&
  isWfShape ([] : StructContext) (panValueShape ([] : StructContext) wordValue) &&
  isWfShape ([] : StructContext) (panValueShape ([] : StructContext) recordValue) &&
  isWfShape namedContext (panValueShape namedContext namedValue)

#eval parityGuard
#guard parityGuard

theorem panValueIsWf_isWfShape_panValueShape_fixture :
    isWfShape namedContext (panValueShape namedContext namedValue) = true :=
  panValueIsWf_isWfShape_panValueShape namedContext namedValue
    (by simp [panValueIsWf, panValueIsWfFields, namedContext, namedValue,
      lookupInfo])

/-! `is_wf_shape_v_drop` (`panPropsScript.sml:63`): dropping a prefix of the
    context preserves value well-formedness. -/

def dropContext : StructContext :=
  [("T", { fields := [], size := 1 }), ("S", { fields := [], size := 1 })]

theorem panValueIsWf_of_drop_fixture :
    panValueIsWf dropContext namedValue = true :=
  panValueIsWf_of_drop dropContext namedValue 1 (by
    simp [panValueIsWf, panValueIsWfFields, dropContext, namedValue, lookupInfo])

def dropGuard : Bool :=
  panValueIsWf (dropContext.drop 1) namedValue &&
  panValueIsWf dropContext namedValue

#eval dropGuard
#guard dropGuard

/-! `is_wf_shape_v_nil` (`panPropsScript.sml:56`): at the empty struct context,
    value well-formedness coincides with shape well-formedness. -/

theorem panValueIsWf_eq_isWfShape_panValueShape_of_nil_fixture :
    isWfShape ([] : StructContext)
        (panValueShape ([] : StructContext) namedValue) =
      panValueIsWf ([] : StructContext) namedValue :=
  panValueIsWf_eq_isWfShape_panValueShape_of_nil ([] : StructContext) namedValue
    rfl

theorem panValueIsWf_of_isWfShape_panValueShape_nil_fixture :
    panValueIsWf ([] : StructContext) recordValue = true :=
  panValueIsWf_of_isWfShape_panValueShape_nil recordValue (by
    simp [panValueShape, isWfShape, isWfShape.isWfShapeList, recordValue])

def nilGuard : Bool :=
  (isWfShape ([] : StructContext)
      (panValueShape ([] : StructContext) wordValue) ==
    panValueIsWf ([] : StructContext) wordValue) &&
  (isWfShape ([] : StructContext)
      (panValueShape ([] : StructContext) recordValue) ==
    panValueIsWf ([] : StructContext) recordValue)

#eval nilGuard
#guard nilGuard

end Flapjack.Test.PanValueWfParity
