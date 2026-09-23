import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack.Test.BackendCommonCarryParity

open Flapjack

/-! Exact numeric outputs from `word_add_carry_probe.out`, produced by the
    original CakeML `backend_common$word_add_carry` on 8-bit words. -/
def carryOutput (left right carry : BitVec 8) : Nat × Nat :=
  let (result, overflow) := wordAddCarryHOL left right carry
  (result.toNat, overflow.toNat)

#guard carryOutput 3 4 0 == (7, 0)
#guard carryOutput 255 1 0 == (0, 1)
#guard carryOutput 3 4 2 == (8, 0)
#guard carryOutput 255 0 1 == (0, 1)

end Flapjack.Test.BackendCommonCarryParity
