import Flapjack.RiscV.PanMemory

/-!
# Little-endian 4-byte OR/shift assembly over `BitVec 32`

This module proves the general little-endian four-byte identity needed by the
exact `panSem$mem_load_32_alt` port (`cakeml/pancake/semantics/panSemScript.sml:108`):

```
(b0 ≪ 0) ‖ (b1 ≪ 8) ‖ (b2 ≪ 16) ‖ (b3 ≪ 24)
  = b0 + 256*b1 + 256^2*b2 + 256^3*b3
```

where the four bytes are `BitVec 8` values and the result is a `BitVec 32`
(the zero-extended `w2w` bytes of the HOL statement).  The right-hand side is the
base-256 assembly implemented by `RiscV.panRiscVWordOfBytes`.

Both the leaf arithmetic and the bitvector statement are untagged: HOL's
`byteScript`/`mem_load_32_alt` are statements about arbitrary word widths, and the
helper `get_byte` lives in HOL stdlib (outside the `cakeml` submodule), so no
`@[hol]` tag is possible.  The big-endian sibling is tracked by
`flapjack-pxn.18.3.6.9.27.2`; the little-endian lemma here is
`flapjack-pxn.18.3.6.9.27.1`.

The proof is deliberately elementary (no `bv_omega` and no Mathlib): it reduces
the `BitVec` statement to `Nat` via `BitVec.eq_of_toNat_eq`, converts each `|||`
into an addition using disjointness (`Nat.shiftLeft_add_eq_or_of_lt`), and matches
the base-256 coefficients with `256 = 2^8`, `256^2 = 2^16`, `256^3 = 2^24`.
-/

namespace Flapjack

/-- A byte shifted by one of the three 32-bit byte offsets stays below the next
power of two.  Used to bound the base-256 sum. -/
theorem memByte_nat_shiftLeft_lt (b : Nat) (hb : b < 256) (i : Nat)
    (hi : i = 8 ∨ i = 16 ∨ i = 24) : b <<< i < 2 ^ (i + 8) := by
  rcases hi with rfl | rfl | rfl
  · rw [Nat.shiftLeft_eq]
    calc b * 2 ^ 8 < 256 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 8)
      _ = 2 ^ 16 := by decide
  · rw [Nat.shiftLeft_eq]
    calc b * 2 ^ 16 < 256 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 16)
      _ = 2 ^ 24 := by decide
  · rw [Nat.shiftLeft_eq]
    calc b * 2 ^ 24 < 256 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 24)
      _ = 2 ^ 32 := by decide

/-- Little-endian four-byte Nat assembly equals the base-256 sum, provided each
byte is below `256`.  The `_h3` hypothesis is retained for symmetry with the HOL
statement even though the last OR is resolved without needing it. -/
theorem memByte_nat_orShift_eq_base256 (b0 b1 b2 b3 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (_h3 : b3 < 256) :
    ((b0 ||| (b1 <<< 8)) ||| (b2 <<< 16)) ||| (b3 <<< 24)
      = b0 + 256 * b1 + 256 ^ 2 * b2 + 256 ^ 3 * b3 := by
  have e1 : b0 ||| (b1 <<< 8) = b0 + (b1 <<< 8) := by
    calc b0 ||| (b1 <<< 8) = (b1 <<< 8) ||| b0 := Nat.or_comm b0 (b1 <<< 8)
      _ = (b1 <<< 8) + b0 := (Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega) b1).symm
      _ = b0 + (b1 <<< 8) := Nat.add_comm (b1 <<< 8) b0
  have t1 : b0 + (b1 <<< 8) < 2 ^ 16 := by
    have hb1 : b1 <<< 8 < 2 ^ 16 := by simpa using memByte_nat_shiftLeft_lt b1 h1 8 (Or.inl rfl)
    omega
  have e2 : (b0 + (b1 <<< 8)) ||| (b2 <<< 16) = b0 + (b1 <<< 8) + (b2 <<< 16) := by
    calc (b0 + (b1 <<< 8)) ||| (b2 <<< 16) = (b2 <<< 16) ||| (b0 + (b1 <<< 8)) :=
          Nat.or_comm (b0 + (b1 <<< 8)) (b2 <<< 16)
      _ = (b2 <<< 16) + (b0 + (b1 <<< 8)) :=
          (Nat.shiftLeft_add_eq_or_of_lt (i := 16) t1 b2).symm
      _ = b0 + (b1 <<< 8) + (b2 <<< 16) := by omega
  have t2 : b0 + (b1 <<< 8) + (b2 <<< 16) < 2 ^ 24 := by
    have hb2 : b2 <<< 16 < 2 ^ 24 :=
      by simpa using memByte_nat_shiftLeft_lt b2 h2 16 (Or.inr (Or.inl rfl))
    have hb1big : b1 <<< 8 < 2 ^ 24 := by
      have := memByte_nat_shiftLeft_lt b1 h1 8 (Or.inl rfl); omega
    omega
  have e3 : (b0 + (b1 <<< 8) + (b2 <<< 16)) ||| (b3 <<< 24)
      = b0 + (b1 <<< 8) + (b2 <<< 16) + (b3 <<< 24) := by
    calc (b0 + (b1 <<< 8) + (b2 <<< 16)) ||| (b3 <<< 24)
          = (b3 <<< 24) ||| (b0 + (b1 <<< 8) + (b2 <<< 16)) :=
            Nat.or_comm (b0 + (b1 <<< 8) + (b2 <<< 16)) (b3 <<< 24)
      _ = (b3 <<< 24) + (b0 + (b1 <<< 8) + (b2 <<< 16)) :=
            (Nat.shiftLeft_add_eq_or_of_lt (i := 24) t2 b3).symm
      _ = b0 + (b1 <<< 8) + (b2 <<< 16) + (b3 <<< 24) := by omega
  rw [e1, e2, e3]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [show (256 : Nat) = 2 ^ 8 from by decide, show 256 ^ 2 = 2 ^ 16 from by decide,
    show 256 ^ 3 = 2 ^ 24 from by decide]
  rw [Nat.mul_comm b1 (2 ^ 8), Nat.mul_comm b2 (2 ^ 16), Nat.mul_comm b3 (2 ^ 24)]

/-- `toNat` of a zero-extended byte shifted by a byte offset: no wraparound at
width 32 for offsets 8, 16, 24. -/
theorem memByte_shiftLeft_toNat (b : BitVec 8) (i : Nat) (hi : i = 8 ∨ i = 16 ∨ i = 24) :
    ((b.setWidth 32).shiftLeft i).toNat = b.toNat <<< i := by
  rw [BitVec.shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)]
  have hb : b.toNat < 256 := by
    have := b.isLt; simpa [show (2 : Nat) ^ 8 = 256 from by decide] using this
  have hlt : b.toNat <<< i < 2 ^ 32 := by
    rcases hi with rfl | rfl | rfl
    · rw [Nat.shiftLeft_eq]
      calc b.toNat * 2 ^ 8 < 256 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 8)
        _ = 2 ^ 16 := by decide
        _ < 2 ^ 32 := by decide
    · rw [Nat.shiftLeft_eq]
      calc b.toNat * 2 ^ 16 < 256 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 16)
        _ = 2 ^ 24 := by decide
        _ < 2 ^ 32 := by decide
    · rw [Nat.shiftLeft_eq]
      calc b.toNat * 2 ^ 24 < 256 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 24)
        _ = 2 ^ 32 := by decide
  rw [Nat.mod_eq_of_lt hlt]

/-- **Little-endian 4-byte equality.** The zero-extended shifted OR of four bytes
(`BitVec 8`) equals the base-256 assembly as a `BitVec 32`, with no side
conditions. -/
theorem memByte32_orShift_eq_base256 (b0 b1 b2 b3 : BitVec 8) :
    (b0.setWidth 32 ||| (b1.setWidth 32) <<< 8 ||| (b2.setWidth 32) <<< 16
        ||| (b3.setWidth 32) <<< 24)
      = BitVec.ofNat 32
          (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) := by
  have hw : (8 : Nat) ≤ 32 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  change (BitVec.setWidth 32 b0).toNat |||
      (BitVec.shiftLeft (BitVec.setWidth 32 b1) 8).toNat |||
      (BitVec.shiftLeft (BitVec.setWidth 32 b2) 16).toNat |||
      (BitVec.shiftLeft (BitVec.setWidth 32 b3) 24).toNat
    = (BitVec.ofNat 32
        (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat)).toNat
  rw [BitVec.toNat_setWidth_of_le hw, memByte_shiftLeft_toNat b1 8 (Or.inl rfl),
    memByte_shiftLeft_toNat b2 16 (Or.inr (Or.inl rfl)),
    memByte_shiftLeft_toNat b3 24 (Or.inr (Or.inr rfl)), BitVec.toNat_ofNat]
  have hb0 : b0.toNat < 256 := by
    have := b0.isLt; simpa [show (2 : Nat) ^ 8 = 256 from by decide] using this
  have hb1 : b1.toNat < 256 := by
    have := b1.isLt; simpa [show (2 : Nat) ^ 8 = 256 from by decide] using this
  have hb2 : b2.toNat < 256 := by
    have := b2.isLt; simpa [show (2 : Nat) ^ 8 = 256 from by decide] using this
  have hb3 : b3.toNat < 256 := by
    have := b3.isLt; simpa [show (2 : Nat) ^ 8 = 256 from by decide] using this
  have hs : b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat < 2 ^ 32 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, show 256 ^ 2 = 2 ^ 16 from by decide,
      show 256 ^ 3 = 2 ^ 24 from by decide, show (2 : Nat) ^ 32 = 4294967296 from by decide]
    omega
  rw [Nat.mod_eq_of_lt hs]
  exact memByte_nat_orShift_eq_base256 b0.toNat b1.toNat b2.toNat b3.toNat hb0 hb1 hb2 hb3

/-- **Big-endian 4-byte equality.** Sibling of `memByte32_orShift_eq_base256`: the
zero-extended shifted OR of four bytes (`BitVec 8`) equals the big-endian base-256
assembly as a `BitVec 32`, with no side conditions. -/
theorem memByte32_orShift_eq_base256_be (b0 b1 b2 b3 : BitVec 8) :
    (b0.setWidth 32) <<< 24 ||| (b1.setWidth 32) <<< 16 ||| (b2.setWidth 32) <<< 8
        ||| (b3.setWidth 32)
      = BitVec.ofNat 32
          (b3.toNat + 256 * b2.toNat + 256 ^ 2 * b1.toNat + 256 ^ 3 * b0.toNat) := by
  simpa only [BitVec.or_assoc, BitVec.or_comm]
    using memByte32_orShift_eq_base256 b3 b2 b1 b0

-- Concrete regression fixtures (the `panRiscVWordOfBytes` tie-in is checked by
-- kernel `decide`; the base-256 value check uses the general theorem).

example : (BitVec.setWidth 32 (0x78 : BitVec 8) ||| (BitVec.setWidth 32 (0x56 : BitVec 8)) <<< 8
    ||| (BitVec.setWidth 32 (0x34 : BitVec 8)) <<< 16
    ||| (BitVec.setWidth 32 (0x12 : BitVec 8)) <<< 24)
    = RiscV.panRiscVWordOfBytes (width := 32) false
        [BitVec.setWidth 32 (0x78 : BitVec 8), BitVec.setWidth 32 (0x56 : BitVec 8),
         BitVec.setWidth 32 (0x34 : BitVec 8), BitVec.setWidth 32 (0x12 : BitVec 8)] := by
  decide

example : (BitVec.setWidth 32 (0 : BitVec 8) ||| (BitVec.setWidth 32 (0 : BitVec 8)) <<< 8
    ||| (BitVec.setWidth 32 (0 : BitVec 8)) <<< 16
    ||| (BitVec.setWidth 32 (255 : BitVec 8)) <<< 24)
    = BitVec.ofNat 32 (256 ^ 3 * 255) := by
  rw [memByte32_orShift_eq_base256]
  rfl

example : ((BitVec.setWidth 32 (0x12 : BitVec 8)) <<< 24 ||| (BitVec.setWidth 32 (0x34 : BitVec 8)) <<< 16
    ||| (BitVec.setWidth 32 (0x56 : BitVec 8)) <<< 8 ||| (BitVec.setWidth 32 (0x78 : BitVec 8)))
    = RiscV.panRiscVWordOfBytes (width := 32) true
        [BitVec.setWidth 32 (0x12 : BitVec 8), BitVec.setWidth 32 (0x34 : BitVec 8),
         BitVec.setWidth 32 (0x56 : BitVec 8), BitVec.setWidth 32 (0x78 : BitVec 8)] := by
  decide

end Flapjack
