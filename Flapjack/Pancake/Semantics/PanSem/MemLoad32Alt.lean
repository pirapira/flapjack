/-
# RV64-specialized analogue of `panSem$mem_load_32_alt` OR/shift assembly

HOL `mem_load_32_alt` (`cakeml/pancake/semantics/panSemScript.sml:108`) restates
`mem_load_32` by assembling the four stored bytes with `w2w` widening and
`<<`/`|||` instead of `word_of_bytes`:

```
mem_load_32 m dm be w =
  if aligned 2 w then case m (byte_align w) of Word v =>
    if byte_align w IN dm then
      let b0 = get_byte w v be in ... let b3 = get_byte (w + 3w) v be in
      let v' = if be then w2w b0 << 24 ||| ... ||| w2w b3
               else w2w b0 ||| w2w b1 << 8 ||| ... << 24 in SOME (v' : word32)
    else NONE else NONE
```

`panMemLoad32HOL` is the tagged exact `mem_load_32_def` port over the total
`HolWordLab` memory shape.  This module proves the untagged equality of
`panMemLoad32HOL` with that OR/shift form at the production width 64.  The
casting steps are: `panGetByteHOL` agrees with the exact codec
`RiscV.panRiscVGetByteEndian` (`get_byte` at width 64), and `w2w` is
`BitVec.ofNat 32 ∘ BitVec.toNat`.

The theorem is deliberately untagged: HOL `mem_load_32_alt` is stated for
arbitrary `'a word`, while this port is width-64-specialized, and the byte
codec `get_byte` lives in HOL stdlib (outside the `cakeml` submodule).  Direct
original-HOL rows are reused from `scripts/hol-probes/pan_sem_state_eval_probe.out`
(`mem_load_32_def_little`, `_big`, `_misaligned`, `_missing`, `_w24_addr4`).
See bead `flapjack-pxn.18.3.6.9.27`.
-/
import Flapjack.Pancake.Semantics.PanSem.MemByteAssembly
import Flapjack.Pancake.Semantics.PanSemStateEval

namespace Flapjack

theorem nat_or4_reverse (a0 a1 a2 a3 : Nat) :
    ((a0 ||| a1) ||| a2) ||| a3 = ((a3 ||| a2) ||| a1) ||| a0 := by
  rw [Nat.or_comm ((a0 ||| a1) ||| a2) a3]
  rw [Nat.or_comm (a0 ||| a1) a2]
  rw [Nat.or_comm a0 a1]
  rw [← Nat.or_assoc a3 a2 (a1 ||| a0), ← Nat.or_assoc (a3 ||| a2) a1 a0]

theorem memByte32_wide_le (b0 b1 b2 b3 : BitVec 32) (h0 : b0.toNat < 256) (h1 : b1.toNat < 256)
    (h2 : b2.toNat < 256) (h3 : b3.toNat < 256) :
    RiscV.panRiscVWordOfBytes (width := 32) false [b0, b1, b2, b3]
      = b0 ||| BitVec.shiftLeft b1 8 ||| BitVec.shiftLeft b2 16 ||| BitVec.shiftLeft b3 24 := by
  simp only [RiscV.panRiscVWordOfBytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  rw [if_neg (by decide : ¬ (false = true))]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  simp only [BitVec.shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b1.toNat <<< 8 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b2.toNat <<< 16 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b3.toNat <<< 24 < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by omega : b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat < 2 ^ 32)]
  exact (memByte_nat_orShift_eq_base256 b0.toNat b1.toNat b2.toNat b3.toNat h0 h1 h2 h3).symm

theorem memByte32_wide_be (b0 b1 b2 b3 : BitVec 32) (h0 : b0.toNat < 256) (h1 : b1.toNat < 256)
    (h2 : b2.toNat < 256) (h3 : b3.toNat < 256) :
    RiscV.panRiscVWordOfBytes (width := 32) true [b0, b1, b2, b3]
      = BitVec.shiftLeft b0 24 ||| BitVec.shiftLeft b1 16 ||| BitVec.shiftLeft b2 8 ||| b3 := by
  have hnat : b0.toNat <<< 24 ||| b1.toNat <<< 16 ||| b2.toNat <<< 8 ||| b3.toNat
      = b3.toNat + 256 * b2.toNat + 256 ^ 2 * b1.toNat + 256 ^ 3 * b0.toNat := by
    rw [nat_or4_reverse (b0.toNat <<< 24) (b1.toNat <<< 16) (b2.toNat <<< 8) b3.toNat]
    exact memByte_nat_orShift_eq_base256 b3.toNat b2.toNat b1.toNat b0.toNat h3 h2 h1 h0
  simp only [RiscV.panRiscVWordOfBytes, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  rw [if_pos trivial]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  simp only [BitVec.shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b0.toNat <<< 24 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b1.toNat <<< 16 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b2.toNat <<< 8 < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by omega : b3.toNat + 256 * b2.toNat + 256 ^ 2 * b1.toNat + 256 ^ 3 * b0.toNat < 2 ^ 32)]
  exact hnat.symm

theorem panGetByteHOL_toNat_lt_256 (address value : RiscV.Word 64) (be : Bool) :
    (panGetByteHOL address value be).toNat < 256 := UInt8.toNat_lt _

theorem panGetByteHOL_toBitVec32_eq_setWidth (address value : RiscV.Word 64) (be : Bool) :
    BitVec.ofNat 32 (panGetByteHOL address value be).toNat =
      BitVec.setWidth 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be) := by
  have h := panGetByteHOL_eq_panRiscVGetByteEndian address value be
  have hlt := panRiscVGetByteEndian_toNat_lt_256 address value be
  have htoNat : (panGetByteHOL address value be).toNat =
      (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat := by
    rw [h, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  rw [htoNat, BitVec.ofNat_toNat]

theorem panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address value : RiscV.Word 64) (be : Bool) :
    (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat).toNat < 256 := by
  have hlt := panRiscVGetByteEndian_toNat_lt_256 address value be
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide : (256 : Nat) ≤ 2 ^ 32))]
  exact hlt

theorem memByte32_map_getByte (address value : RiscV.Word 64) (be : Bool) :
    RiscV.panRiscVWordOfBytes (width := 32) be
        [BitVec.ofNat 32 (panGetByteHOL address value be).toNat,
         BitVec.ofNat 32 (panGetByteHOL (address + 1) value be).toNat,
         BitVec.ofNat 32 (panGetByteHOL (address + 2) value be).toNat,
         BitVec.ofNat 32 (panGetByteHOL (address + 3) value be).toNat]
      = (if be then
          BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat) 24
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value be).toNat) 16
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value be).toNat) 8
            ||| BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value be).toNat
        else
          BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value be).toNat) 8
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value be).toNat) 16
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value be).toNat) 24) := by
  rw [panGetByteHOL_toBitVec32_eq_setWidth address value be,
    panGetByteHOL_toBitVec32_eq_setWidth (address + 1) value be,
    panGetByteHOL_toBitVec32_eq_setWidth (address + 2) value be,
    panGetByteHOL_toBitVec32_eq_setWidth (address + 3) value be]
  rw [← BitVec.ofNat_toNat, ← BitVec.ofNat_toNat, ← BitVec.ofNat_toNat, ← BitVec.ofNat_toNat]
  cases be
  · exact memByte32_wide_le _ _ _ _
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 address value false)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 1) value false)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 2) value false)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 3) value false)
  · exact memByte32_wide_be _ _ _ _
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 address value true)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 1) value true)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 2) value true)
      (panRiscVGetByteEndian_ofNat32_toNat_lt_256 (address + 3) value true)

theorem panGetByteHOL_ofNat64_toNat (address value : RiscV.Word 64) (be : Bool) :
    (BitVec.ofNat 64 (panGetByteHOL address value be).toNat).toNat =
      (panGetByteHOL address value be).toNat := by
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (panGetByteHOL_toNat_lt_256 address value be) (by decide : (256 : Nat) ≤ 2 ^ 64))]

theorem panRiscVWordOfBytes_map_getByte_eq (value : RiscV.Word 64) (address : RiscV.Word 64)
    (be : Bool) :
    RiscV.panRiscVWordOfBytes (width := 32) be
        ([BitVec.ofNat 64 (panGetByteHOL address value be).toNat,
          BitVec.ofNat 64 (panGetByteHOL (address + 1) value be).toNat,
          BitVec.ofNat 64 (panGetByteHOL (address + 2) value be).toNat,
          BitVec.ofNat 64 (panGetByteHOL (address + 3) value be).toNat].map
            (fun byte => BitVec.ofNat 32 byte.toNat))
      = (if be then
          BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat) 24
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value be).toNat) 16
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value be).toNat) 8
            ||| BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value be).toNat
        else
          BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value be).toNat
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value be).toNat) 8
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value be).toNat) 16
            ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value be).toNat) 24) := by
  simp only [List.map_cons, List.map_nil]
  rw [panGetByteHOL_ofNat64_toNat address value be,
    panGetByteHOL_ofNat64_toNat (address + 1) value be,
    panGetByteHOL_ofNat64_toNat (address + 2) value be,
    panGetByteHOL_ofNat64_toNat (address + 3) value be]
  exact memByte32_map_getByte address value be

theorem panMemLoad32HOL_eq_alt (memory : RiscV.Word 64 → HolWordLab 64)
    (domain : RiscV.Word 64 → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word 64) :
    panMemLoad32HOL memory domain bigEndian address =
      (if address.toNat % 4 = 0 then
        let aligned := panByteAlignHOL (width := 64) address
        match memory aligned with
        | .word value =>
            if domain aligned then
              some (if bigEndian then
                BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value bigEndian).toNat) 24
                  ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value bigEndian).toNat) 16
                  ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value bigEndian).toNat) 8
                  ||| BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value bigEndian).toNat
              else
                BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value bigEndian).toNat
                  ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) value bigEndian).toNat) 8
                  ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) value bigEndian).toNat) 16
                  ||| BitVec.shiftLeft (BitVec.ofNat 32 (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) value bigEndian).toNat) 24)
            else none
      else none) := by
  simp only [panMemLoad32HOL]
  split
  · split
    · congr 1
      exact panRiscVWordOfBytes_map_getByte_eq
        (memory (panByteAlignHOL (width := 64) address)).1 address bigEndian
    · rfl
  · rfl

end Flapjack
