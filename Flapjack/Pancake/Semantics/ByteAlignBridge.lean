import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.CrepSem.Eval

/-!
# Agreement of the source and target byte-codec renderings

HOL `byte$byte_align_def` (`src/n-bit/alignmentScript.sml:23`) is
`byte_align (w : 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w`, i.e. the low
`LOG2 (width DIV 8)` address bits are cleared.

The source-side byte codec renders this as `panByteAlignHOL` (division and
multiplication by `2 ^ LOG2 (width / 8)`) and the target-side codec as
`riscvByteAlignHOL` (shift out and back). The read side is rendered as
`panGetByteHOL` (`cell.toNat / 256 ^ byteIndex`) and `riscvGetByteHOL`
(`(value >>> 8 * byteIndex).toNat % 256`). This module proves the renderings
agree for every word width and address, which is the alignment and byte-read
half of the source/target byte-store correspondence
(`Flapjack/Pancake/CrepToLoop/StateRel.lean`, HOL `write_bytearray_mem_rel`).
Both helpers are Flapjack-specific renderings of HOL standard-library formulas
that live outside the CakeML submodule, so these declarations carry no `@[hol]`
tag. -/

namespace Flapjack

/-- `riscvByteAlignHOL` and `panByteAlignHOL` compute the same HOL `byte_align`
    address. -/
theorem riscvByteAlignHOL_eq_panByteAlignHOL {width : Nat} [NeZero width]
    (address : RiscV.Word width) :
    riscvByteAlignHOL address = panByteAlignHOL address := by
  simp only [riscvByteAlignHOL, panByteAlignHOL]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

/-- `256 ^ b = 2 ^ (8 * b)`: the source `panGetByteHOL` divides by a power of
    `256`, the target `riscvGetByteHOL` shifts by eight times the byte index. -/
theorem pow256_eq_two_pow_mul (b : Nat) : (256 : Nat) ^ b = 2 ^ (8 * b) := by
  rw [Nat.pow_mul, show (256 : Nat) = 2 ^ 8 from by decide]

/-- `panGetByteHOL` and `riscvGetByteHOL` read the same byte of a word
    (HOL `byte$get_byte_def`/`byte_index_def`), for both endiannesses. -/
theorem panGetByteHOL_eq_riscvGetByteHOL {width : Nat} [NeZero width]
    (address value : RiscV.Word width) (bigEndian : Bool) :
    panGetByteHOL address value bigEndian = riscvGetByteHOL bigEndian address value := by
  cases bigEndian <;>
    simp only [panGetByteHOL, riscvGetByteHOL, if_true, if_false, Bool.false_eq_true,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow256_eq_two_pow_mul]

/-- Bit index (within a word) of the byte selected by `address`; shared by the
    source `panSetByteHOL` and the target `riscvSetByteHOL` byte-writes. -/
def byteBitIndex {width : Nat} (address : RiscV.Word width) (bigEndian : Bool) : Nat :=
  if bigEndian then 8 * (width / 8 - 1 - address.toNat % (width / 8))
  else 8 * (address.toNat % (width / 8))

private theorem byteBitIndex_add_eight_le {width : Nat} [NeZero width]
    (hdiv : width % 8 = 0) (address : RiscV.Word width) (bigEndian : Bool) :
    byteBitIndex address bigEndian + 8 ≤ width := by
  have hw : 8 * (width / 8) = width := by
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)]
  have hpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have hd : 0 < width / 8 := by omega
  have hlt : address.toNat % (width / 8) < width / 8 := Nat.mod_lt _ hd
  cases bigEndian <;>
    simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;>
    omega

/-- Boundedness of the three disjoint byte slices: the preserved low slice, the
    inserted byte, and the preserved high slice. Flapjack proof infrastructure
    for the byte-write decomposition. -/
private theorem byteSetBound (v b K width : Nat) (hb : b < 2 ^ 8) (hv : v < 2 ^ width)
    (hK : K + 8 ≤ width) :
    v % 2 ^ K + b * 2 ^ K + v / 2 ^ (K + 8) * 2 ^ (K + 8) < 2 ^ width := by
  have hmid : b * 2 ^ K + v % 2 ^ K < 2 ^ (K + 8) := by
    have hb' : b * 2 ^ K ≤ (2 ^ 8 - 1) * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
    have hl : v % 2 ^ K < 2 ^ K := Nat.mod_lt _ (Nat.two_pow_pos K)
    have hsum := Nat.add_lt_add_of_le_of_lt hb' hl
    have h2 : (2 ^ 8 - 1) * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
      have h3 : (2 ^ 8 - 1) * 2 ^ K + 2 ^ K = ((2 ^ 8 - 1) + 1) * 2 ^ K := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [h3, show (2 ^ 8 - 1 + 1 : Nat) = 2 ^ 8 from by decide,
        show (2 : Nat) ^ 8 * 2 ^ K = 2 ^ (K + 8) from by rw [Nat.pow_add, Nat.mul_comm]]
    rwa [h2] at hsum
  have hupper : v / 2 ^ (K + 8) * 2 ^ (K + 8) ≤ 2 ^ width - 2 ^ (K + 8) := by
    have hp : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
    have hdvd : 2 ^ (K + 8) ∣ 2 ^ width := Nat.pow_dvd_pow 2 hK
    have hle : v / 2 ^ (K + 8) * 2 ^ (K + 8) ≤ v := Nat.div_mul_le_self _ _
    have hlt : v / 2 ^ (K + 8) * 2 ^ (K + 8) < 2 ^ width := Nat.lt_of_le_of_lt hle hv
    have hq : v / 2 ^ (K + 8) < 2 ^ width / 2 ^ (K + 8) :=
      (Nat.lt_div_iff_mul_lt_of_dvd (by omega) hdvd).mpr hlt
    have hsucc : (v / 2 ^ (K + 8) + 1) * 2 ^ (K + 8) ≤ 2 ^ width :=
      (Nat.le_div_iff_mul_le hp).mp (Nat.succ_le_of_lt hq)
    rw [Nat.add_mul, Nat.one_mul] at hsucc
    rw [Nat.le_sub_iff_add_le (Nat.pow_le_pow_right (by omega) hK)]
    exact hsucc
  have hfin := Nat.add_lt_add_of_lt_of_le hmid hupper
  have hgt : 2 ^ (K + 8) + (2 ^ width - 2 ^ (K + 8)) = 2 ^ width :=
    Nat.add_sub_cancel' (Nat.pow_le_pow_right (by omega) hK)
  rw [hgt] at hfin
  omega

set_option linter.unusedSimpArgs false in
/-- `toNat`-level decomposition of the source `panSetByteHOL` byte-write: the
    preserved low slice, the inserted byte, and the preserved high slice occupy
    the disjoint bit ranges below, at, and above `byteBitIndex`. Flapjack proof
    infrastructure for the width-multiple case; no separate HOL declaration. -/
theorem panSetByteHOL_toNat {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    (address value : RiscV.Word width) (byte : UInt8) (bigEndian : Bool) :
    (panSetByteHOL address (BitVec.ofNat width byte.toNat) value bigEndian).toNat =
      (value.toNat / 2 ^ (byteBitIndex address bigEndian + 8)) *
          2 ^ (byteBitIndex address bigEndian + 8) +
        byte.toNat * 2 ^ byteBitIndex address bigEndian +
        value.toNat % 2 ^ byteBitIndex address bigEndian := by
  have hw : 8 * (width / 8) = width := by
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)]
  have hw8 : 8 ≤ width := by
    have := Nat.pos_of_ne_zero (NeZero.ne width); omega
  have hb8 : byte.toNat < 2 ^ 8 := by
    have := byte.toNat_lt_size; simpa [UInt8.size] using this
  have hbyte : byte.toNat % 2 ^ width % 256 = byte.toNat := by
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) hw8)),
      show (256 : Nat) = 2 ^ 8 from by decide]
    exact Nat.mod_eq_of_lt hb8
  cases bigEndian
  · have hK8 : byteBitIndex address false + 8 ≤ width :=
      byteBitIndex_add_eight_le hdiv address false
    have hoff : (256 : Nat) ^ (address.toNat % (width / 8)) = 2 ^ byteBitIndex address false := by
      rw [pow256_eq_two_pow_mul]
      simp only [byteBitIndex, Bool.false_eq_true, if_false]
    have hmod := byteSetBound value.toNat byte.toNat (byteBitIndex address false) width
      hb8 value.isLt hK8
    unfold panSetByteHOL
    simp only [Bool.false_eq_true, if_false, BitVec.toNat_ofNat]
    rw [hoff, hbyte, show 2 ^ byteBitIndex address false * 256 =
        2 ^ (byteBitIndex address false + 8) from by
      rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_add]]
    rw [Nat.mod_eq_of_lt hmod]
    omega
  · have hK8 : byteBitIndex address true + 8 ≤ width :=
      byteBitIndex_add_eight_le hdiv address true
    have hoff : (256 : Nat) ^ (width / 8 - address.toNat % (width / 8) - 1) =
        2 ^ byteBitIndex address true := by
      rw [pow256_eq_two_pow_mul]
      simp only [byteBitIndex, if_true]
      rw [Nat.sub_right_comm]
    have hmod := byteSetBound value.toNat byte.toNat (byteBitIndex address true) width
      hb8 value.isLt hK8
    unfold panSetByteHOL
    simp only [if_true, BitVec.toNat_ofNat]
    rw [hoff, hbyte, show 2 ^ byteBitIndex address true * 256 =
        2 ^ (byteBitIndex address true + 8) from by
      rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_add]]
    rw [Nat.mod_eq_of_lt hmod]
    omega

set_option linter.unusedSimpArgs false in
private theorem getLsbD_mask_or_shift {width : Nat} (value : BitVec width) (byte : UInt8)
    (K i : Nat) (hi : i < width) :
    ((value &&& ~~~((BitVec.ofNat width 0xFF) <<< K)) |||
        ((BitVec.ofNat width byte.toNat) <<< K)).getLsbD i =
      (if i < K then value.getLsbD i
       else if i < K + 8 then byte.toNat.testBit (i - K) else value.getLsbD i) := by
  have hb8 : byte.toNat < 2 ^ 8 := by have := byte.toNat_lt_size; simpa [UInt8.size] using this
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 from by decide]
  by_cases h1 : i < K
  · have h2 : i < K + 8 := by omega
    simp [h1, h2, hi]
  · rw [if_neg h1]
    by_cases h2 : i < K + 8
    · rw [if_pos h2]
      have h8 : i - K < 8 := by omega
      have hwK : i - K < width := by omega
      have h255 : (2 ^ 8 - 1).testBit (i - K) = true := by
        rw [Nat.testBit_two_pow_sub_one]; simp [h8]
      simp [h1, h2, h8, hwK, hi, h255, Nat.add_zero]
    · rw [if_neg h2]
      have hj : 8 ≤ i - K := by omega
      have h8 : ¬ i - K < 8 := by omega
      have hb : byte.toNat.testBit (i - K) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) hj))
      have h255 : (2 ^ 8 - 1).testBit (i - K) = false := by
        rw [Nat.testBit_two_pow_sub_one]; simp [h8]
      simp [h1, h2, hb, h255, hi, Nat.add_zero]

set_option linter.unusedSimpArgs false in
private theorem getLsbD_holFinite {width : Nat} (value : BitVec width) (byte : UInt8)
    (K i : Nat) (hi : i < width) :
    ((((value >>> (K + 8)) <<< (K + 8)) |||
        ((BitVec.setWidth width (BitVec.extractLsb' 0 8 (BitVec.ofNat width byte.toNat))) <<< K)) |||
      BitVec.setWidth width (BitVec.extractLsb' 0 K value)).getLsbD i =
      (if i < K then value.getLsbD i
       else if i < K + 8 then byte.toNat.testBit (i - K) else value.getLsbD i) := by
  have hb8 : byte.toNat < 2 ^ 8 := by have := byte.toNat_lt_size; simpa [UInt8.size] using this
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat]
  by_cases h1 : i < K
  · have h2 : i < K + 8 := by omega
    simp [h1, h2, hi]
  · rw [if_neg h1]
    by_cases h2 : i < K + 8
    · rw [if_pos h2]
      have h8 : i - K < 8 := by omega
      have hwK : i - K < width := by omega
      simp [h1, h2, h8, hwK, hi, Nat.add_zero]
    · rw [if_neg h2]
      have hj : 8 ≤ i - K := by omega
      have h8 : ¬ i - K < 8 := by omega
      have hb : byte.toNat.testBit (i - K) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) hj))
      have e : K + 8 + (i - (K + 8)) = i := by omega
      simp [h1, h2, hb, e, hi, Nat.add_zero]

theorem riscvSetByteHOL_eq_holFiniteWordSetByteBitVec {width : Nat} [NeZero width]
    (address value : RiscV.Word width) (byte : UInt8) (bigEndian : Bool) :
    riscvSetByteHOL bigEndian address value byte =
      holFiniteWordSetByteBitVec width (byteBitIndex address bigEndian)
        (BitVec.ofNat width byte.toNat) value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show riscvSetByteHOL bigEndian address value byte =
        ((value &&& ~~~((BitVec.ofNat width 0xFF) <<< byteBitIndex address bigEndian)) |||
          ((BitVec.ofNat width byte.toNat) <<< byteBitIndex address bigEndian)) from rfl,
      show holFiniteWordSetByteBitVec width (byteBitIndex address bigEndian)
          (BitVec.ofNat width byte.toNat) value =
        ((((value >>> (byteBitIndex address bigEndian + 8)) <<<
              (byteBitIndex address bigEndian + 8)) |||
            ((BitVec.setWidth width
                (BitVec.extractLsb' 0 8 (BitVec.ofNat width byte.toNat))) <<<
              byteBitIndex address bigEndian)) |||
          BitVec.setWidth width (BitVec.extractLsb' 0 (byteBitIndex address bigEndian) value))
        from rfl,
      getLsbD_mask_or_shift value byte (byteBitIndex address bigEndian) i hi,
      getLsbD_holFinite value byte (byteBitIndex address bigEndian) i hi]

/-- The source `panSetByteHOL` and the target `riscvSetByteHOL` write the same
    byte (the byte-write half of HOL `write_bytearray_mem_rel`; the byte-read
    half is `panGetByteHOL_eq_riscvGetByteHOL`). Requires `width` a whole number
    of bytes, matching the word widths the compiler produces. -/
theorem panSetByteHOL_eq_riscvSetByteHOL {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    (address value : RiscV.Word width) (byte : UInt8) (bigEndian : Bool) :
    panSetByteHOL address (BitVec.ofNat width byte.toNat) value bigEndian =
      riscvSetByteHOL bigEndian address value byte := by
  apply BitVec.eq_of_toNat_eq
  rw [panSetByteHOL_toNat hdiv address value byte bigEndian,
    riscvSetByteHOL_eq_holFiniteWordSetByteBitVec address value byte bigEndian]
  have hw8 : 8 ≤ width := by
    have hw : 8 * (width / 8) = width := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)]
    have := Nat.pos_of_ne_zero (NeZero.ne width); omega
  have hb8 : byte.toNat < 2 ^ 8 := by
    have := byte.toNat_lt_size; simpa [UInt8.size] using this
  have hbyte2 : (BitVec.ofNat width byte.toNat).toNat % 2 ^ 8 = byte.toNat := by
    have h1 : byte.toNat % 2 ^ width = byte.toNat :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) hw8))
    rw [BitVec.toNat_ofNat, h1]
    exact Nat.mod_eq_of_lt hb8
  rw [holFiniteWordSetByteBitVec_toNat _ _ _ _
    (byteBitIndex_add_eight_le hdiv address bigEndian), hbyte2]

end Flapjack
