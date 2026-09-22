import Flapjack.RiscV.PanSemantics
import Flapjack.PanValueFlatten

/-!
# Crepe `crep_primop`

Source reference:
`cakeml/pancake/semantics/crepSemScript.sml:221-232`.

The Crepe primitive boundary accepts exactly a three-word `AddCarry` operand
list.  It returns the low word and the carry bit as two words and rejects all
other arities or operators, matching the original source definition.
-/

namespace Flapjack.RiscV

def crepPrimop [NeZero width] :
    CrepPrimitiveHandler (Word width)
  | .addCarry, [left, right, carry] =>
      let (result, carryOut) := addCarryWords left right carry
      some [result, carryOut]
  | _, _ => none

theorem crepPrimop_eq_handler [NeZero width]
    (operator : PrimOp) (arguments : List (Word width)) :
    crepPrimop operator arguments = crepPrimitiveHandler operator arguments := by
  rfl

/-- Cake's `pan_primop_crep_primop`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096`): flattening the
    value produced by the Pancake primitive handler yields exactly the word
    list produced by the Crepe primitive handler on the flattened arguments.
    `panValueFlatten` is the Flapjack counterpart of Cake's `flatten`. -/
theorem panPrimitiveHandler_crepPrimitiveHandler [NeZero width]
    (operator : PrimOp) (values : List (PanValue (Word width)))
    (value : PanValue (Word width))
    (h : panPrimitiveHandler operator values = some value) :
    crepPrimitiveHandler operator (panValueFlattenValues values) =
      some (panValueFlatten value) := by
  cases operator
  cases values with
  | nil => simp [panPrimitiveHandler] at h
  | cons first rest =>
      cases rest with
      | nil => simp [panPrimitiveHandler] at h
      | cons second rest2 =>
          cases rest2 with
          | nil => simp [panPrimitiveHandler] at h
          | cons third rest3 =>
              cases rest3 with
              | cons _ _ => simp [panPrimitiveHandler] at h
              | nil =>
                  cases first with
                  | word left =>
                      cases second with
                      | word right =>
                          cases third with
                          | word carry =>
                              simp [panPrimitiveHandler] at h
                              rw [← h]
                              simp [panValueFlattenValues, panValueFlatten,
                                crepPrimitiveHandler]
                          | rStruct fields => simp [panPrimitiveHandler] at h
                          | nStruct name fields => simp [panPrimitiveHandler] at h
                      | rStruct fields => simp [panPrimitiveHandler] at h
                      | nStruct name fields => simp [panPrimitiveHandler] at h
                  | rStruct fields => simp [panPrimitiveHandler] at h
                  | nStruct name fields => simp [panPrimitiveHandler] at h

end Flapjack.RiscV
