import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# Byte set/get roundtrip for the Pancake memory proof

HOL `byte$set_byte_get_byte` (`HOL/src/n-bit/byteScript.sml:847`) states

    `8 <= dimindex (:'a) ==> set_byte a (get_byte (a:'a word) (w:'a word) be) w be = w`

i.e. writing back the byte read at an address reproduces the original word.
`panGetByteHOL`/`panSetByteHOL` are Flapjack's width-indexed renderings of HOL
`get_byte`/`set_byte`; that script is part of the HOL standard library rather
than the CakeML submodule, so these declarations carry no `@[hol]` tag (matching
`Flapjack/Pancake/Semantics/ByteAlignBridge.lean` and the byte helpers in
`LoopSem.lean`).

The width-indexed roundtrip here is the prerequisite for the exact
`read_write_bytearray_lemma` port (`cakeml/pancake/semantics/panPropsScript.sml:1119`),
whose `read_bytearray`/`write_bytearray` use `panGetByteHOL`/`panSetByteHOL`
through `panMemLoadByteHOL`/`panMemStoreByteHOL`. -/

namespace Flapjack

/-- Flapjack-specific arithmetic: reassembling the low `8`-bit slice, the next
    `8`-bit slice and the remaining high bits recovers a natural number.  The
    identity underlying the byte roundtrip; it has no HOL theorem original (HOL
    proves the same fact through `word_slice_alt` bit manipulation). -/
theorem nat_byte_reconstruct (v offset : Nat) :
    v % offset + ((v / offset) % 256) * offset + (v / (offset * 256)) * (offset * 256) = v := by
  have hq : (v / offset) % 256 + 256 * (v / (offset * 256)) = v / offset := by
    have h1 := Nat.mod_add_div (v / offset) 256
    rw [Nat.div_div_eq_div_mul] at h1
    exact h1
  have hmul : (((v / offset) % 256) + 256 * (v / (offset * 256))) * offset
      = ((v / offset) % 256) * offset + (v / (offset * 256)) * (offset * 256) := by
    rw [Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm 256 (v / (offset * 256) * offset), ← Nat.mul_assoc]
  calc
    v % offset + ((v / offset) % 256) * offset + (v / (offset * 256)) * (offset * 256)
        = v % offset +
            (((v / offset) % 256) * offset + (v / (offset * 256)) * (offset * 256)) := by
            ac_rfl
    _ = v % offset + (((v / offset) % 256) + 256 * (v / (offset * 256))) * offset := by
            rw [hmul]
    _ = v % offset + (v / offset) * offset := by rw [hq]
    _ = v := by rw [Nat.mul_comm (v / offset) offset, Nat.mod_add_div]

/-- `toNat`-level roundtrip: storing the byte `panGetByteHOL` reads at `address`
    back into `value` reproduces `value`, for any word width at least a byte.
    This is the Lean analogue of the body of HOL `byte$set_byte_get_byte`
    (`HOL/src/n-bit/byteScript.sml:847`); see the module docstring for why it
    carries no `@[hol]` tag. -/
theorem panSetByteHOL_panGetByteHOL_toNat {width : Nat}
    (address value : RiscV.Word width) (bigEndian : Bool) (hwidth : 8 ≤ width) :
    (panSetByteHOL address
        (BitVec.ofNat width (panGetByteHOL address value bigEndian).toNat) value bigEndian).toNat =
      value.toNat := by
  have h8 : 256 ≤ 2 ^ width := by
    calc (256 : Nat) = 2 ^ 8 := by decide
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hwidth
  cases bigEndian
  · simp only [Bool.false_eq_true, if_false, panSetByteHOL, panGetByteHOL,
      BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_mod]
    have h1 : (BitVec.toNat value / 256 ^ (BitVec.toNat address % (width / 8))) % 256 <
        2 ^ width := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) h8
    have h2 : (BitVec.toNat value / 256 ^ (BitVec.toNat address % (width / 8))) % 256 <
        256 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    rw [nat_byte_reconstruct (BitVec.toNat value)
      (256 ^ (BitVec.toNat address % (width / 8)))]
    rw [Nat.mod_eq_of_lt value.isLt]
  · simp only [if_true, panSetByteHOL, panGetByteHOL,
      BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_mod]
    rw [Nat.sub_right_comm (width / 8) 1 (BitVec.toNat address % (width / 8))]
    have h1 : (BitVec.toNat value / 256 ^ (width / 8 - BitVec.toNat address % (width / 8) - 1)) % 256 <
        2 ^ width := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) h8
    have h2 : (BitVec.toNat value / 256 ^ (width / 8 - BitVec.toNat address % (width / 8) - 1)) % 256 <
        256 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    rw [nat_byte_reconstruct (BitVec.toNat value)
      (256 ^ (width / 8 - BitVec.toNat address % (width / 8) - 1))]
    rw [Nat.mod_eq_of_lt value.isLt]

/-- Width-generic byte roundtrip: `panSetByteHOL` writing back the byte
    `panGetByteHOL` read at `address` leaves the word unchanged.  Lean analogue
    of HOL `byte$set_byte_get_byte` (`HOL/src/n-bit/byteScript.sml:847`); see the
    module docstring for why it carries no `@[hol]` tag. -/
theorem panSetByteHOL_panGetByteHOL {width : Nat}
    (address value : RiscV.Word width) (bigEndian : Bool) (hwidth : 8 ≤ width) :
    panSetByteHOL address
        (BitVec.ofNat width (panGetByteHOL address value bigEndian).toNat) value bigEndian =
      value := by
  apply BitVec.eq_of_toNat_eq
  rw [panSetByteHOL_panGetByteHOL_toNat address value bigEndian hwidth]

/-- Width-32 instantiation of the byte roundtrip. -/
theorem panSetByteHOL_panGetByteHOL_32 (address value : RiscV.Word 32)
    (bigEndian : Bool) :
    panSetByteHOL address
        (BitVec.ofNat 32 (panGetByteHOL address value bigEndian).toNat) value bigEndian =
      value :=
  panSetByteHOL_panGetByteHOL address value bigEndian (by decide)

/-- Width-64 instantiation of the byte roundtrip. -/
theorem panSetByteHOL_panGetByteHOL_64 (address value : RiscV.Word 64)
    (bigEndian : Bool) :
    panSetByteHOL address
        (BitVec.ofNat 64 (panGetByteHOL address value bigEndian).toNat) value bigEndian =
      value :=
  panSetByteHOL_panGetByteHOL address value bigEndian (by decide)

end Flapjack
