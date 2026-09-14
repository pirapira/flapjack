import Flapjack.RiscV.PanSemantics

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

end Flapjack.RiscV
