import Flapjack.PanValues
import Flapjack.RiscV.Model

/-!
RISC-V word semantics for Pancake's source-level `AddCarry` primitive.

CakeML defines the primitive over fixed-width words: the result is the
low-width part of `left + right + carry`, and the second field records whether
the mathematical sum overflowed the word width.  The generic source evaluator
receives this operation through `PanPrimitiveHandler`, keeping the source
language independent of the chosen target word representation.
-/

namespace Flapjack.RiscV

def addCarryWords [NeZero width] (left right carry : Word width) :
    Word width × Word width :=
  let total := left.toNat + right.toNat + if carry == 0 then 0 else 1
  (BitVec.ofNat width total,
    BitVec.ofNat width (if 2 ^ width ≤ total then 1 else 0))

def panPrimitiveHandler [NeZero width] :
    PanPrimitiveHandler (Word width)
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, carryOut) := addCarryWords left right carry
      some (.rStruct [.word result, .word carryOut])
  | _, _ => none

theorem addCarryWords_no_overflow [NeZero width]
    (left right : Word width) :
    (addCarryWords left right (BitVec.ofNat width 0)).2 =
      BitVec.ofNat width
        (if 2 ^ width ≤ left.toNat + right.toNat then 1 else 0) := by
  simp [addCarryWords]

theorem panPrimitiveHandler_addCarry [NeZero width]
    (left right : Word width) :
    panPrimitiveHandler .addCarry
      [.word left, .word right, .word (BitVec.ofNat width 0)] =
      some (.rStruct [
        .word (BitVec.ofNat width (left.toNat + right.toNat)),
        .word (BitVec.ofNat width
          (if 2 ^ width ≤ left.toNat + right.toNat then 1 else 0))]) := by
  simp [panPrimitiveHandler, addCarryWords]

end Flapjack.RiscV
