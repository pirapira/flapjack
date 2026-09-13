import Flapjack.Loop
import Flapjack.LoopSemantics

namespace Flapjack

/--
Faithful port of the original CakeML Pancake `loop_arith` definition.

Reference: `cakeml/pancake/semantics/loopSemScript.sml:118-145` (`loop_arith_def`).
Word values are modelled as unbounded `Nat`s; `width` fixes the original
`dimword (:'a) = 2 ^ width` so the word operations can be reproduced exactly.
-/
def loopArithDiv (destination dividend divisor : Nat) (locals : Nat → Option Nat) :
    Option (Nat → Option Nat) :=
  match locals divisor, locals dividend with
  | some q, some dividendValue =>
      if q = 0 then none
      else some (updateLoopLocal locals destination (dividendValue / q))
  | _, _ => none

/--
Faithful port of the `LLongMul` branch of `loop_arith`.

The original writes the low word first as an inner update and the high word as
the outer update, so the high word wins when both destinations coincide.
-/
def loopArithLongMul (width destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (locals : Nat → Option Nat) : Option (Nat → Option Nat) :=
  match locals sourceLeft, locals sourceRight with
  | some leftValue, some rightValue =>
      let base := 2 ^ width
      let product := leftValue * rightValue
      let withHigh := updateLoopLocal locals destinationLeft (product / base % base)
      some (updateLoopLocal withHigh destinationRight (product % base))
  | _, _ => none

/--
Faithful port of the `LLongDiv` branch of `loop_arith`.

The original writes the remainder as the inner update and the quotient as the
outer update, so the quotient wins when both destinations coincide.
-/
def loopArithLongDiv (width destinationLeft destinationRight sourceLeft sourceRight quotient :
    Nat) (locals : Nat → Option Nat) : Option (Nat → Option Nat) :=
  match locals sourceLeft, locals sourceRight, locals quotient with
  | some high, some low, some divisor =>
      let base := 2 ^ width
      let numerator := high * base + low
      let result := numerator / divisor
      if divisor ≠ 0 ∧ result < base then
        let withRemainder := updateLoopLocal locals destinationRight (numerator % divisor)
        some (updateLoopLocal withRemainder destinationLeft result)
      else none
  | _, _, _ => none

/-- Faithful port of `loop_arith` covering `LDiv`, `LLongMul`, and `LLongDiv`. -/
def loopArith (width : Nat) : LoopArith → (Nat → Option Nat) → Option (Nat → Option Nat)
  | .div destination dividend divisor, locals =>
      loopArithDiv destination dividend divisor locals
  | .longMul destinationLeft destinationRight sourceLeft sourceRight, locals =>
      loopArithLongMul width destinationLeft destinationRight sourceLeft sourceRight locals
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient, locals =>
      loopArithLongDiv width destinationLeft destinationRight sourceLeft sourceRight quotient locals

end Flapjack
