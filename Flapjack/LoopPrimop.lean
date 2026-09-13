import Flapjack.LoopSemantics
import Flapjack.RiscV.PanSemantics

/-!
# Pancake Loop primitive semantics

This is the RISC-V-word instance of `loop_primop` from
`cakeml/pancake/semantics/loopSemScript.sml:242-252`.  CakeML currently has
one Loop primitive, `AddCarry`; malformed arity or any other primitive returns
`none`, while a valid triple returns the low word and the carry word.
-/

namespace Flapjack.RiscV

def loopPrimop [NeZero width] : PrimOp → List (Word width) → Option (List (Word width))
  | .addCarry, [left, right, carry] =>
      let (result, carryOut) := addCarryWords left right carry
      some [result, carryOut]
  | _, _ => none

theorem loopPrimop_eq_handler [NeZero width] (operator : PrimOp)
    (arguments : List (Word width)) :
    loopPrimop operator arguments = loopPrimitiveHandler operator arguments := by
  rfl

end Flapjack.RiscV
