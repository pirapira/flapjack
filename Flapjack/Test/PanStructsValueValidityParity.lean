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

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def pairName : ExactName := .implode [80, 97, 105, 114]
private def outerName : ExactName := .implode [79, 117, 116, 101, 114]
private def prefixName : ExactName := .implode [80, 114, 101, 102, 105, 120, 79, 110, 108, 121]
private def leftName : ExactName := .implode [108, 101, 102, 116]
private def rightName : ExactName := .implode [114, 105, 103, 104, 116]
private def innerName : ExactName := .implode [105, 110, 110, 101, 114]
private def tagName : ExactName := .implode [116, 97, 103]
private def markerName : ExactName := .implode [109, 97, 114, 107, 101, 114]

private def exactNestedContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName,
      { fields := [(leftName, .one), (rightName, .comb [])], size := 2 }),
   (outerName,
      { fields := [(innerName, .named pairName), (tagName, .one)], size := 2 })]

private def exactAppendPrefix : Flapjack.Pancake.PanLang.StructContextExact :=
  [(prefixName, { fields := [(markerName, .one)], size := 1 })]

private def exactNestedValue : ValueHOL 8 :=
  .nStruct outerName
    [(innerName,
      .nStruct pairName
        [(leftName, .val (.word 2)), (rightName, .rStruct [])]),
     (tagName, .val (.word 3))]

private def exactValueValidityContext : StructContextHOLM :=
  [(pairName,
    { fields := [(leftName, .one), (rightName, .comb [])], size := 2 })]

private def exactValueValidityMatch : ValueHOL 8 :=
  .nStruct pairName
    [(leftName, .val (.word 2)), (rightName, .rStruct [])]

private def exactValueValidityMismatch : ValueHOL 8 :=
  .nStruct pairName
    [(leftName, .val (.word 2)), (markerName, .rStruct [])]

private def exactValueValidityFirstMatchContext : StructContextHOLM :=
  [(pairName, { fields := [(markerName, .one)], size := 1 }),
   (pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 })]

private def exactValueValiditySecondMatchContext : StructContextHOLM :=
  [(pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 }),
   (pairName, { fields := [(markerName, .one)], size := 1 })]

private def holValueValidityMismatch : PanValue Nat :=
  .nStruct "Pair" [("left", .word 2), ("wrong", .rStruct [])]

/-- Exact-carrier `is_wf_shape_v_word` row from the original HOL oracle. -/
example : panIsWfShapeValueHOLExact exactValueValidityContext
    (.val (.word 1) : ValueHOL 8) = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux]

/-- Exact-carrier `is_wf_shape_v_named_match` HOL oracle row. -/
example : panIsWfShapeValueHOLExact exactValueValidityContext exactValueValidityMatch = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactValueValidityContext, exactValueValidityMatch]

/-- Exact-carrier `is_wf_shape_v_named_missing` HOL oracle row. -/
example : panIsWfShapeValueHOLExact ([] : StructContextHOLM)
    exactValueValidityMatch = false := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactValueValidityMatch]

/-- HOL ignores field names in `is_wf_shape_v`, so this exact-carrier mismatch
    still follows the positive original-HOL oracle row. -/
example : panIsWfShapeValueHOLExact exactValueValidityContext
    exactValueValidityMismatch = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactValueValidityContext, exactValueValidityMismatch]

/-- Exact-carrier duplicate-key regression. The predicate observes only whether
    `ALOOKUP` succeeds, so either duplicate order remains positive. -/
example : panIsWfShapeValueHOLExact exactValueValidityFirstMatchContext
    exactValueValidityMatch = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactValueValidityFirstMatchContext, exactValueValidityMatch]

example : panIsWfShapeValueHOLExact exactValueValiditySecondMatchContext
    exactValueValidityMatch = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactValueValiditySecondMatchContext, exactValueValidityMatch]

/-- Exact-carrier recursive named-struct case from the direct HOL oracle. -/
example : panIsWfShapeValueHOLExact exactNestedContext exactNestedValue = true := by
  simp [panIsWfShapeValueHOLExact, panIsWfShapeValueHOLExactAux,
    panIsWfShapeValuesHOLExactAux,
    panPropsALookupEq, exactNestedContext, exactNestedValue,
    pairName, outerName, leftName, rightName, innerName, tagName]

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

/-- Context whose first `Pair` entry is the good one, so first-match lookup wins
    positively; the second entry is shadowed. -/
private def holValueValiditySecondMatchContext : StructContextHOL :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 }),
   ("Pair", { fields := [("wrong", Shape.one)], size := 1 })]

private def valueValiditySecondMatchContext : StructContext :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 }),
   ("Pair", { fields := [("wrong", Shape.one)], size := 1 })]

/-- A context with a nested named struct field. -/
private def nestedContext : StructContextHOL :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 }),
   ("Outer", { fields := [("inner", Shape.named "Pair"), ("tag", Shape.one)], size := 2 })]

private def nestedContextList : StructContext :=
  [("Pair", { fields := [("left", Shape.one), ("right", Shape.comb [])], size := 2 }),
   ("Outer", { fields := [("inner", Shape.named "Pair"), ("tag", Shape.one)], size := 2 })]

private def nestedValue : PanValue Nat :=
  .nStruct "Outer"
    [("inner", .nStruct "Pair" [("left", .word 2), ("right", .rStruct [])]),
     ("tag", .word 3)]

private def appendPrefix : StructContextHOL :=
  [("PrefixOnly", { fields := [("marker", Shape.one)], size := 1 })]

/-- `v_flds_ok_duplicate_second` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk holValueValiditySecondMatchContext holValueValidityMatch = true := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    panStructShapeListEqBool, panStructShapeEqBool, panSemShapeOf,
    holValueValiditySecondMatchContext, holValueValidityMatch]

/-- `is_wf_shape_v_duplicate_second` in `pan_structs_value_validity_probe.out`. -/
example : panIsWfShapeValueHOL holValueValiditySecondMatchContext holValueValidityMatch = true := by
  simp [panIsWfShapeValueHOL, panIsWfShapeValuesHOL, lookupInfo,
    holValueValiditySecondMatchContext, holValueValidityMatch]

/-- `v_flds_ok_nested_match` in `pan_structs_value_validity_probe.out`. -/
example : panValueFldsOk nestedContext nestedValue = true := by
  simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
    panStructShapeListEqBool, panStructShapeEqBool, panSemShapeOf,
    nestedContext, nestedValue]

/-- `v_flds_ok_append_nonempty_prefix_named` in the direct HOL-EVAL fixture. -/
example : panValueFldsOk (appendPrefix ++ nestedContext) nestedValue = true := by
  apply panValueFldsOk_append appendPrefix nestedContext nestedValue
  · simp [panValueFldsOk, panValuesFldsOk, panFieldsFldsOk, lookupInfo,
      panStructShapeListEqBool, panStructShapeEqBool, panSemShapeOf,
      nestedContext, nestedValue]
  · simp [appendPrefix, nestedContext]

/-- Exact `panSem$v` / `mlstring` regression for the named nonempty-prefix HOL
    EVAL row `v_flds_ok_append_nonempty_prefix_named`. -/
example : valueFldsOkHOLExact (exactAppendPrefix ++ exactNestedContext)
    exactNestedValue = true := by
  apply valueFldsOkHOLExact_append exactNestedContext exactAppendPrefix exactNestedValue
  · simp [valueFldsOkHOLExact, valuesFldsOkHOLExact, fieldsFldsOkHOLExact,
      Flapjack.Pancake.PanLang.structContextLookupHOL, shapeOfHOLExact,
      shapeEqHOL, shapeEqHOL.shapeEqListHOL, exactNestedContext,
      exactNestedValue, pairName, outerName, leftName, rightName,
      innerName, tagName]
  · simp [exactAppendPrefix, exactNestedContext, prefixName, pairName, outerName,
      leftName, rightName, innerName, tagName]

/-- `is_wf_shape_v_nested_match` in `pan_structs_value_validity_probe.out`. -/
example : panIsWfShapeValueHOL nestedContext nestedValue = true := by
  simp [panIsWfShapeValueHOL, panIsWfShapeValuesHOL, lookupInfo,
    nestedContext, nestedValue]

/-! ## Adapters between the exact HOL-shaped predicates and the production
    cache-augmented-context predicates, under `StructContext.toHOL`. -/

/-- `v_flds_ok` adapter at the matching fixture. -/
example :
    panValueFldsOk valueValidityContext.toHOL holValueValidityMatch =
      panStructValueFieldsOkBool valueValidityContext valueValidityMatch :=
  panValueFldsOk_toHOL valueValidityContext holValueValidityMatch

/-- `v_flds_ok` adapter at the first-match-shadowing fixture. -/
example :
    panValueFldsOk valueValiditySecondMatchContext.toHOL holValueValidityMatch =
      panStructValueFieldsOkBool valueValiditySecondMatchContext valueValidityMatch :=
  panValueFldsOk_toHOL valueValiditySecondMatchContext holValueValidityMatch

/-- `v_flds_ok` adapter at the nested named-struct fixture. -/
example :
    panValueFldsOk nestedContextList.toHOL nestedValue =
      panStructValueFieldsOkBool nestedContextList nestedValue :=
  panValueFldsOk_toHOL nestedContextList nestedValue

/-- `is_wf_shape_v` adapter at the matching fixture. -/
example :
    panIsWfShapeValueHOL valueValidityContext.toHOL holValueValidityMatch =
      panIsWfShapeValueBool valueValidityContext valueValidityMatch :=
  panIsWfShapeValueHOL_toHOL valueValidityContext holValueValidityMatch

/-- `is_wf_shape_v` adapter at the nested named-struct fixture. -/
example :
    panIsWfShapeValueHOL nestedContextList.toHOL nestedValue =
      panIsWfShapeValueBool nestedContextList nestedValue :=
  panIsWfShapeValueHOL_toHOL nestedContextList nestedValue

/-- The projection from the cache-augmented context preserves lookup shadowing. -/
example :
    lookupInfo "Pair" valueValidityFirstMatchContext.toHOL =
      some { fields := [("wrong", Shape.one)], size := 1 } := by
  simp [StructContext.toHOL, valueValidityFirstMatchContext, lookupInfo]

/-- Direct check of the tagged HOL `fdoms_eq_flookup_some_none` on concrete maps. -/
example :
    ∃ v', FLOOKUP (fun n : Nat => if n = 2 then some 20 else none) 2 = some v' :=
  fdoms_eq_flookup_some_none (fun n : Nat => if n = 2 then some 20 else none)
    (fun n : Nat => if n = 2 then some 20 else none) 2 20 0 rfl rfl

/-- A map with the same domain but a different value still defines the lookup. -/
example :
    ∃ v', FLOOKUP (fun n : Nat => if n = 2 then some 99 else none) 2 = some v' :=
  fdoms_eq_flookup_some_none (fun n : Nat => if n = 2 then some 20 else none)
    (fun n : Nat => if n = 2 then some 99 else none) 2 20 0 (by
      funext k
      by_cases hk : k = 2 <;> simp [FDOM, hk]) rfl

end Flapjack.Test
