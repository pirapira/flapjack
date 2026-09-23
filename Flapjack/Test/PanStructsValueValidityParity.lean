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
    panStructFieldValuesFieldsOkBool, panStructShapeListEqBool,
    panStructShapeEqBool, panSemShapeOf, lookupInfo, valueValidityContext,
    valueValidityMatch]

example : panStructValueFieldsOkBool valueValidityContext valueValidityMismatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panStructShapeListEqBool,
    panStructShapeEqBool, panSemShapeOf, lookupInfo, valueValidityContext,
    valueValidityMismatch]

example : panStructValueFieldsOkBool [] valueValidityMatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, lookupInfo, valueValidityMatch]

example : panStructValueFieldsOkBool valueValidityFirstMatchContext
    valueValidityMatch = false := by
  simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panStructShapeListEqBool,
    panStructShapeEqBool, panSemShapeOf, lookupInfo,
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

end Flapjack.Test
