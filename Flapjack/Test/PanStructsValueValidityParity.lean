import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect

/-! Lean cases paired with `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/

namespace Flapjack.Test

open Flapjack

private def valueValidityContext : StructContext :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 })]

private def valueValidityMatch : PanValue Nat :=
  .nStruct "Pair" [("left", .word 2), ("right", .rStruct [])]

private def valueValidityMismatch : PanValue Nat :=
  .nStruct "Pair" [("left", .word 2), ("wrong", .rStruct [])]

private def valueValidityFirstMatchContext : StructContext :=
  [("Pair", { fields := [("wrong", Shape.one)], size := 1 }),
   ("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 })]

example (name : String) (structs : StructContext) :
    lookupInfo name structs = panPropsALookupEq name structs := by
  exact lookupInfo_eq_panPropsALookupEq name structs

example :
    panStructContextShapeView valueValidityContext =
      [("Pair", [("left", Shape.one), ("right", Shape.comb [])])] := rfl

example : panStructValueFieldsOkBool valueValidityContext (.word 1 : PanValue Nat) = true := by
  simp [panStructValueFieldsOkBool, valueValidityContext]

example : panStructValueFieldsOkBool valueValidityContext valueValidityMatch = true := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panValueFieldsHaveShapes,
    panShapeMatches, panShapeMatches.panShapeListMatches, panValueShape, lookupInfo,
    valueValidityContext, valueValidityMatch]

example : panStructValueFieldsOkBool valueValidityContext valueValidityMismatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panValueFieldsHaveShapes,
    panShapeMatches, panShapeMatches.panShapeListMatches, panValueShape, lookupInfo,
    valueValidityContext, valueValidityMismatch]

example : panStructValueFieldsOkBool [] valueValidityMatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, lookupInfo, valueValidityMatch]

example : panStructValueFieldsOkBool valueValidityFirstMatchContext
    valueValidityMatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panValueFieldsHaveShapes,
    panShapeMatches, panValueShape, lookupInfo,
    valueValidityFirstMatchContext, valueValidityMatch]

example : panIsWfShapeValueBool valueValidityContext (.word 1 : PanValue Nat) = true := by
  simp [panIsWfShapeValueBool, valueValidityContext]

example : panIsWfShapeValueBool valueValidityContext valueValidityMatch = true := by
  simp [panIsWfShapeValueBool, panIsWfShapeValuesBool,
    panIsWfShapeValueFieldsBool, lookupInfo, valueValidityContext,
    valueValidityMatch]

example : panIsWfShapeValueBool [] valueValidityMatch = false := by
  simp [panIsWfShapeValueBool, panIsWfShapeValuesBool,
    panIsWfShapeValueFieldsBool, lookupInfo, valueValidityMatch]

example : panStructShapeListEqBool [.comb []] [.comb []] = true := by
  simp [panStructShapeListEqBool, panStructShapeEqBool]

private def holValueValidityContext : StructContextHOL :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 })]

private def holValueValidityFirstMatchContext : StructContextHOL :=
  [("Pair", { fields := [("wrong", Shape.one)], size := 1 }),
   ("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 })]

private def holValueValidityMatch : PanValue Nat :=
  .nStruct "Pair" [("left", .word 2), ("right", .rStruct [])]

private def holValueValidityMismatch : PanValue Nat :=
  .nStruct "Pair" [("left", .word 2), ("wrong", .rStruct [])]

/-- `v_flds_ok_word` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk holValueValidityContext (.word 1 : PanValue Nat) = true := by
  simp [panValueFldsOk, holValueValidityContext]

/-- `v_flds_ok_named_match` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk holValueValidityContext holValueValidityMatch = true := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    panStructShapeListEqBool, panStructShapeEqBool, panSemShapeOf,
    holValueValidityContext, holValueValidityMatch]

/-- `v_flds_ok_named_mismatch` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk holValueValidityContext holValueValidityMismatch = false := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    holValueValidityContext, holValueValidityMismatch]

/-- `v_flds_ok_named_missing` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk ([] : StructContextHOL) holValueValidityMatch = false := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    holValueValidityMatch]

/-- `is_wf_shape_v_named_mismatch` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk holValueValidityContext holValueValidityMismatch = false := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    holValueValidityContext, holValueValidityMismatch]

/-- `is_wf_shape_v_word` in `pan_structs_value_validity_probe.out`. -/
example : panIsWfShapeValueHOL holValueValidityContext (.word 1 : PanValue Nat) = true := by
  simp [panIsWfShapeValueHOL, holValueValidityContext]

/-- `is_wf_shape_v_named_match` in `pan_structs_value_validity_probe.out`. -/
example : panIsWfShapeValueHOL holValueValidityContext holValueValidityMatch = true := by
  simp [panIsWfShapeValueHOL, panIsWfShapeValuesHOL, lookupInfo,
    holValueValidityContext, holValueValidityMatch]

/-- `is_wf_shape_v_named_missing` in `pan_structs_value_validity_probe.out`. -/
example : panIsWfShapeValueHOL ([] : StructContextHOL) holValueValidityMatch = false := by
  simp [panIsWfShapeValueHOL, panIsWfShapeValuesHOL, lookupInfo, holValueValidityMatch]

/-- `is_wf_shape_v_named_mismatch` in `pan_structs_value_validity_probe.out`:
    `is_wf_shape_v` ignores field names, so the renamed field still counts. -/
example : panIsWfShapeValueHOL holValueValidityContext holValueValidityMismatch = true := by
  simp [panIsWfShapeValueHOL, panIsWfShapeValuesHOL, lookupInfo,
    holValueValidityContext, holValueValidityMismatch]

end Flapjack.Test
