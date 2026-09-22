import Flapjack.PanValueFlatten

/-!
# Original-domain parity for HOL `panSem$flatten`

Fixtures mirror the original Pancake helpers
`length_flatten_eq_size_of_shape` (`cakeml/pancake/semantics/panPropsScript.sml:171`)
and `flatten_nil_no_size`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3001`).
-/

namespace Flapjack.Test.PanValueFlattenParity

open Flapjack

def wordValue : PanValue Nat := .word 5

def recordValue : PanValue Nat := .rStruct [.word 1, .word 2, .word 3]

def nestedValue : PanValue Nat := .rStruct [.rStruct [.word 1, .word 2], .word 3]

theorem panValueFlatten_word_fixture : panValueFlatten wordValue = [5] := by
  simp [wordValue, panValueFlatten]

theorem panValueFlatten_record_fixture : panValueFlatten recordValue = [1, 2, 3] := by
  simp [recordValue, panValueFlatten, panValueFlattenValues]

theorem panValueFlatten_nested_fixture : panValueFlatten nestedValue = [1, 2, 3] := by
  simp [nestedValue, panValueFlatten, panValueFlattenValues]

theorem nestedValue_wf :
    isWfShape ([] : StructContext) (panValueShape ([] : StructContext) nestedValue) = true := by
  simp [nestedValue, panValueShape, isWfShape, isWfShape.isWfShapeList]

theorem panValueFlatten_length_eq_shapeSize_fixture :
    (panValueFlatten nestedValue).length =
      Shape.shapeSize (panValueShape ([] : StructContext) nestedValue) :=
  panValueFlatten_length_eq_shapeSize nestedValue nestedValue_wf

theorem panValueFlatten_eq_nil_iff_shapeSize_eq_zero_fixture :
    panValueFlatten nestedValue = [] ↔
      Shape.shapeSize (panValueShape ([] : StructContext) nestedValue) = 0 :=
  panValueFlatten_eq_nil_iff_shapeSize_eq_zero nestedValue nestedValue_wf

theorem shapeSize_comb_map_panValueShape_eq_flatten_length_fixture :
    Shape.shapeSize (.comb ([nestedValue, wordValue].map (panValueShape ([] : StructContext)))) =
      ([nestedValue, wordValue].map panValueFlatten).flatten.length :=
  shapeSize_comb_map_panValueShape_eq_flatten_length [nestedValue, wordValue]
    (by
      intro value hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact nestedValue_wf
      · simp [wordValue, panValueShape, isWfShape])

theorem shapeSize_eq_zero_or_flatten_length_fixture :
    ([1, 2, 3] : List Nat).length =
      Shape.shapeSize (panValueShape ([] : StructContext) recordValue) := by
  apply shapeSize_eq_zero_or_flatten_length
  · simp [recordValue, panValueShape, isWfShape, isWfShape.isWfShapeList]
  · intro hzero
    simp [recordValue, panValueShape, Shape.shapeSize] at hzero
  · intro _
    simp [recordValue, panValueFlatten, panValueFlattenValues]

#check @panValueFlatten
#check @panValueFlatten_length_eq_shapeSize
#check @panValueFlatten_eq_nil_iff_shapeSize_eq_zero
#check @shapeSize_comb_map_panValueShape_eq_flatten_length
#check @shapeSize_eq_zero_or_flatten_length
#check @shapeSize_comb_eq_flatten_length_of_getElem

theorem shapeSize_comb_eq_flatten_length_of_getElem_fixture :
    Shape.shapeSize (.comb [panValueShape ([] : StructContext) nestedValue,
        panValueShape ([] : StructContext) wordValue]) =
      ([nestedValue, wordValue].map panValueFlatten).flatten.length := by
  apply shapeSize_comb_eq_flatten_length_of_getElem
  · simp
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by
      simp only [List.length_cons, List.length_nil] at hi
      omega
    rcases hi' with rfl | rfl <;> simp
  · intro arg hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact nestedValue_wf
    · simp [wordValue, panValueShape, isWfShape]

end Flapjack.Test.PanValueFlattenParity
