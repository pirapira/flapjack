import Flapjack.HolRef

/-!
The word-arithmetic helper shared by Pancake's Pan, Crep, and Loop primitive
semantics. Its source is CakeML's `compiler/backend/backend_commonScript.sml`.
-/

namespace Flapjack

/-- HOL `backend_common$word_add_carry`: interpret any nonzero carry input as
    one, return the low word and a one-word overflow flag. The HOL word type
    always has positive width, represented here by `NeZero width`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "word_add_carry_def"]
def wordAddCarryHOL {width : Nat} [NeZero width]
    (left right carry : BitVec width) : BitVec width × BitVec width :=
  let result := left.toNat + right.toNat + (if carry == 0 then 0 else 1)
  (BitVec.ofNat width result,
    if 2 ^ width ≤ result then BitVec.ofNat width 1 else BitVec.ofNat width 0)

end Flapjack
