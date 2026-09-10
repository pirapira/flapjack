import Flapjack.RiscV.PanSemantics

/-!
RISC-V primitive correspondence at the source-to-Crep boundary.

Crep receives the flattened words produced by Pancake's structured
`addCarry` primitive.  This equation is the handler invariant used by the
primitive case of the compiler correctness induction.
-/

namespace Flapjack

theorem RiscV.crepPrimitiveHandler_addCarry_flatten
    [NeZero width] (left right carry : RiscV.Word width) :
    RiscV.crepPrimitiveHandler .addCarry [left, right, carry] =
      (RiscV.panPrimitiveHandler .addCarry
        [.word left, .word right, .word carry]).map panValueFlatWords := by
  simp [RiscV.crepPrimitiveHandler, RiscV.panPrimitiveHandler,
    RiscV.addCarryWords, panValueFlatWords, panValueFlatValueFuel,
    panValueFlatWordsFuel] <;> rfl

end Flapjack
