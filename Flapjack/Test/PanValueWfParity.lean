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

end Flapjack.Test.PanValueWfParity
