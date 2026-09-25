import Flapjack.Pancake.Semantics.PanProps

/-! Exact-carrier parity for HOL `panProps$is_wf_shape_of_v`
(`panPropsScript.sml:38`, bead flapjack-4ac.4.6). -/

namespace Flapjack.Test

open Flapjack

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def pairName : ExactName := .implode [80, 97, 105, 114]
private def leftName : ExactName := .implode [108, 101, 102, 116]
private def rightName : ExactName := .implode [114, 105, 103, 104, 116]

private def exactPairContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 })]

private def exactWordValue : ValueHOL 8 := .val (.word 1)

private def exactMatchingValue : ValueHOL 8 :=
  .nStruct pairName [(leftName, .val (.word 2)), (rightName, .rStruct [])]

/-- Premise of the port at a `Val`: `is_wf_shape_v` holds trivially. -/
example : isWfShapeValueHOLExact exactPairContext exactWordValue = true := by
  simp [isWfShapeValueHOLExact, exactWordValue]

/-- `is_wf_shape_of_v` at a `Val`: `shape_of (Val w) = One`, which is well-formed. -/
example :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL exactPairContext
      (shapeOfHOLExact exactWordValue) = true :=
  isWfShapeValueHOLExact_shapeOfHOLExact exactPairContext exactWordValue
    (by simp [isWfShapeValueHOLExact, exactWordValue])

/-- Premise of the port at a matching named struct. -/
example : isWfShapeValueHOLExact exactPairContext exactMatchingValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
    exactMatchingValue, pairName]

/-- `is_wf_shape_of_v` at a matching named struct. -/
example :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL exactPairContext
      (shapeOfHOLExact exactMatchingValue) = true :=
  isWfShapeValueHOLExact_shapeOfHOLExact exactPairContext exactMatchingValue
    (by
      simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
        Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
        exactMatchingValue, pairName])

end Flapjack.Test
