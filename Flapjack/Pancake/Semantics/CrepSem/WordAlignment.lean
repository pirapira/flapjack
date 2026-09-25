import Init.Data.BitVec.Lemmas

namespace Flapjack

/-- BitVec's Nat shifts implement HOL's `aligned 2` test at every width:
    clearing the low two bits is equivalent to divisibility by four. This
    standalone core-level lemma is shared by Crep source evaluator bridges. -/
theorem bitVecAligned4_iff_shiftGuard {width : Nat}
    (address : BitVec width) :
    ((address >>> 2) <<< 2 = address) ↔ address.toNat % 4 = 0 := by
  have hshift : ((address >>> 2) <<< 2).toNat =
      (address.toNat / 4 * 4) % 2 ^ width := by
    change (BitVec.shiftLeft (BitVec.ushiftRight address 2) 2).toNat = _
    simp only [BitVec.shiftLeft_eq, BitVec.ushiftRight_eq,
      BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have haddress : address.toNat < 2 ^ width := address.isLt
  have hshiftlt : address.toNat / 4 * 4 < 2 ^ width := by
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self address.toNat 4) haddress
  constructor
  · intro heq
    have hnat := congrArg BitVec.toNat heq
    rw [hshift, Nat.mod_eq_of_lt hshiftlt] at hnat
    have hdecomp := Nat.mod_add_div address.toNat 4
    omega
  · intro hmod
    apply BitVec.eq_of_toNat_eq
    rw [hshift, Nat.mod_eq_of_lt hshiftlt]
    have hdecomp := Nat.mod_add_div address.toNat 4
    omega

/-- Boolean guard form of `bitVecAligned4_iff_shiftGuard`. -/
theorem bitVecAligned4_decide_eq_shiftGuard {width : Nat}
    (address : BitVec width) :
    decide (address.toNat % 4 = 0) =
      decide (((address >>> 2) <<< 2) = address) := by
  have hp := bitVecAligned4_iff_shiftGuard address
  cases hleft : decide (address.toNat % 4 = 0) <;>
    cases hright : decide (((address >>> 2) <<< 2) = address) <;> simp_all

end Flapjack
