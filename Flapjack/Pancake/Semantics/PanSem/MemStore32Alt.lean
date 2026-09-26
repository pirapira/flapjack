import Flapjack.Pancake.Semantics.PanSem.MemLoad32Alt

/-! Arbitrary-positive-width port of HOL `panSem$mem_store_32_alt` (`cakeml/pancake/semantics/panSemScript.sml:344`)
    over the HOL-shaped memory carrier.

    HOL states `mem_store_32 m dm be w hw` two equivalent ways: the definition
    (`panMemStore32HOL`, ported from `mem_store_32_def`) extracts bytes with
    `get_byte i hw be`, while the alternative form writes the bytes obtained by
    shifting `hw`: for little endian `w2w hw`, `w2w (hw >>> 8)`, `w2w (hw >>> 16)`,
    `w2w (hw >>> 24)` at `w`, `w+1`, `w+2`, `w+3`, and the big-endian order is the
    reverse. HOL's `w2w` conversions are represented by `BitVec.ofNat width`,
    and `panSetByteHOL` implements the low-byte behavior of `set_byte`. The
    arbitrary HOL word width is represented by any positive Lean BitVec width.
    `get_byte` and `set_byte` are HOL standard-library operations outside the
    CakeML repository; their equations are proved directly for this carrier. -/

namespace Flapjack

/-- `panSetByteHOL` depends on its byte argument only through `.toNat % 256`. -/
theorem panSetByteHOL_congr {width : Nat} (address cell : RiscV.Word width)
    (bigEndian : Bool) {left right : RiscV.Word width}
    (h : left.toNat % 256 = right.toNat % 256) :
    panSetByteHOL address left cell bigEndian =
      panSetByteHOL address right cell bigEndian := by
  unfold panSetByteHOL
  rw [h]

/-- `n / 256^k = n >>> (8*k)`. -/
theorem nat_div_256_pow_eq_shift (n k : Nat) : n / 256 ^ k = n >>> (8 * k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The `toNat` of `panGetByteHOL` at width 32 is the shifted byte of the value. -/
theorem panGetByteHOL32_toNat (i : Nat) (hi : i < 4) (value : BitVec 32)
    (bigEndian : Bool) :
    (panGetByteHOL (width := 32) (BitVec.ofNat 32 i) value bigEndian).toNat =
      (value.toNat >>> (8 * (if bigEndian then 3 - i else i))) % 256 := by
  have hlt : i < 2 ^ 32 := by omega
  have hmod : (BitVec.ofNat 32 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hmod4 : i % 4 = i := Nat.mod_eq_of_lt hi
  unfold panGetByteHOL
  simp only [hmod, hmod4]
  rw [UInt8.toNat_ofNat']
  have hbi : (if bigEndian then 4 - 1 - i else i) = (if bigEndian then 3 - i else i) := by
    split <;> omega
  rw [hbi, Nat.mod_mod, nat_div_256_pow_eq_shift]

/-- `w2w` conversions preserve the low byte observed by `set_byte`, even when
    the destination word is narrower than one byte. -/
theorem ofNat_toNat_mod_256_congr {width : Nat} [NeZero width]
    (left right : Nat) (h : left % 256 = right % 256) :
    (BitVec.ofNat width left).toNat % 256 =
      (BitVec.ofNat width right).toNat % 256 := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  by_cases hwide : 8 ≤ width
  · have hdiv : 256 ∣ 2 ^ width := by
      refine ⟨2 ^ (width - 8), ?_⟩
      calc
        2 ^ width = 2 ^ (8 + (width - 8)) := by congr 1 <;> omega
        _ = 2 ^ 8 * 2 ^ (width - 8) := Nat.pow_add _ _ _
        _ = 256 * 2 ^ (width - 8) := by rw [show (2 : Nat) ^ 8 = 256 by decide]
    rw [Nat.mod_mod_of_dvd _ hdiv, Nat.mod_mod_of_dvd _ hdiv, h]
  · have hdiv : 2 ^ width ∣ 256 := by
      refine ⟨2 ^ (8 - width), ?_⟩
      calc
        256 = 2 ^ 8 := by decide
        _ = 2 ^ (width + (8 - width)) := by congr 1 <;> omega
        _ = 2 ^ width * 2 ^ (8 - width) := Nat.pow_add _ _ _
    have hlow : left % 2 ^ width = right % 2 ^ width := by
      rw [← Nat.mod_mod_of_dvd left hdiv, ← Nat.mod_mod_of_dvd right hdiv, h]
    have hbound : 2 ^ width ≤ 256 := by
      have hw : width ≤ 7 := by omega
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hw
      have hseven : (2 : Nat) ^ 7 = 128 := by decide
      rw [hseven] at hp
      omega
    have hpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have hmodwidth_left : left % 2 ^ width < 2 ^ width := Nat.mod_lt _ (Nat.pow_pos (by omega))
    have hmodwidth_right : right % 2 ^ width < 2 ^ width := Nat.mod_lt _ (Nat.pow_pos (by omega))
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmodwidth_left hbound),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmodwidth_right hbound)]
    exact hlow

/-- The byte-slot congruence underlying the store chain. -/
theorem store32ByteCongr {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bigEndian : Bool)
    (i : Nat) (hi : i < 4) (value : RiscV.Word 32) (current : RiscV.Word width) :
    panSetByteHOL (address + BitVec.ofNat width i)
        (BitVec.ofNat width
          (panGetByteHOL (width := 32) (BitVec.ofNat 32 i) value bigEndian).toNat)
        current bigEndian =
      panSetByteHOL (address + BitVec.ofNat width i)
        (BitVec.ofNat width
          ((value.toNat >>> (8 * (if bigEndian then 3 - i else i))) % 256))
        current bigEndian := by
  apply panSetByteHOL_congr
  rw [panGetByteHOL32_toNat i hi value bigEndian]

/-- The store chain written with `get_byte`, mirroring `panMemStore32HOL`. -/
def store32Orig {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bigEndian : Bool) (value : RiscV.Word 32)
    (cell : RiscV.Word width) : RiscV.Word width :=
  let getByte := fun (index : Nat) =>
    panGetByteHOL (width := 32) (BitVec.ofNat 32 index) value bigEndian
  let setByte := fun (index : Nat) (byte : UInt8) (current : RiscV.Word width) =>
    panSetByteHOL (address + BitVec.ofNat width index) (BitVec.ofNat width byte.toNat)
      current bigEndian
  let cell0 := setByte 0 (getByte 0) cell
  let cell1 := setByte 1 (getByte 1) cell0
  let cell2 := setByte 2 (getByte 2) cell1
  let cell3 := setByte 3 (getByte 3) cell2
  cell3

/-- The store chain written with shifted bytes, mirroring HOL `mem_store_32_alt`. -/
def store32Alt {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bigEndian : Bool) (value : RiscV.Word 32)
    (cell : RiscV.Word width) : RiscV.Word width :=
  let altByte := fun (index : Nat) =>
    BitVec.ofNat width ((value.toNat >>> (8 * (if bigEndian then 3 - index else index))) % 256)
  let setByte := fun (index : Nat) (byte : RiscV.Word width) (current : RiscV.Word width) =>
    panSetByteHOL (address + BitVec.ofNat width index) byte current bigEndian
  let cell0 := setByte 0 (altByte 0) cell
  let cell1 := setByte 1 (altByte 1) cell0
  let cell2 := setByte 2 (altByte 2) cell1
  let cell3 := setByte 3 (altByte 3) cell2
  cell3

/-- The two store chains agree after the byte-slot congruence. -/
theorem store32Orig_eq_alt {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bigEndian : Bool)
    (value : RiscV.Word 32) (cell : RiscV.Word width) :
    store32Orig address bigEndian value cell = store32Alt address bigEndian value cell := by
  simp only [store32Orig, store32Alt]
  rw [store32ByteCongr address bigEndian 0 (by decide) value,
    store32ByteCongr address bigEndian 1 (by decide) value,
    store32ByteCongr address bigEndian 2 (by decide) value,
    store32ByteCongr address bigEndian 3 (by decide) value]

/-- `panMemStore32HOL` with its chain named as `store32Orig`. -/
theorem panMemStore32HOL_eq_orig {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (value : RiscV.Word 32) :
    panMemStore32HOL (width := width) memory domain bigEndian address value =
      if address.toNat % 4 = 0 then
        let aligned := panByteAlignHOL (width := width) address
        match memory aligned with
        | .word cell =>
            if domain aligned then
              some (fun current =>
                if current = aligned then .word (store32Orig address bigEndian value cell)
                else memory current)
            else none
        else none := by
  simp only [panMemStore32HOL, store32Orig]

/-- Arbitrary-positive-width port of HOL `panSem$mem_store_32_alt`: its
    shifted-byte store chain equals the `get_byte` chain from
    `mem_store_32_def`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_store_32_alt"]
theorem panMemStore32HOL_eq_alt {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (value : RiscV.Word 32) :
    panMemStore32HOL (width := width) memory domain bigEndian address value =
      if address.toNat % 4 = 0 then
        let aligned := panByteAlignHOL (width := width) address
        match memory aligned with
        | .word cell =>
            if domain aligned then
              some (fun current =>
                if current = aligned then .word (store32Alt address bigEndian value cell)
                else memory current)
            else none
        else none := by
  rw [panMemStore32HOL_eq_orig]
  simp only [store32Orig_eq_alt]

end Flapjack
