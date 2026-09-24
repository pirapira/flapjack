import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.Compiler.Backend.WordToStack

/-!
# Executable Cake bitmap words vs the tagged HOL recursion (untagged bridge)

The executable CakeML-bitmap helpers in `Flapjack/RiscV/CakeAllocatorCore.lean`
(`bitsToWord`, `frameBitmapWordsAux`, `frameBitmapWords`, `writeBitmap`) are the
`Nat`-valued implementations used by the Cake allocator.  Their HOL originals
(`bits_to_word_def`/`word_list_def` in
`cakeml/compiler/backend/word_to_stackScript.sml`) are polymorphic over the word
carrier.  This module proves, for every input (no range restriction), that the
executable recursion maps onto the tagged width-indexed Lean recursion
`bitsToWordW`/`wordListW`:

* `bitsToWord_ofNat_eq` : `BitVec.ofNat width (bitsToWord bits) = bitsToWordW bits`
  for arbitrary `bits`.  `CakeAlloc.bitsToWord` is exactly the `Nat` value of the
  HOL recursion, and `BitVec.ofNat` performs the same `mod 2^width` truncation
  that HOL's fixed-width `'a word` arithmetic does.  In particular an input whose
  `LENGTH` exceeds `width` wraps: both sides keep only the low `width` bits.

* `frameBitmapWordsAux_map`/`frameBitmapWords_map` : mapping each `Nat` bitmap
  word through `BitVec.ofNat width` reproduces `wordListW` exactly.

These lemmas are deliberately **untagged**.  The remaining, already-documented
mismatch is upstream of the recursion: `writeBitmap` builds the Boolean bitmap
from a list of `names` (`List.contains`), whereas HOL `write_bitmap` uses
`toAList live` and `MEM` over a finite map.  Bridging that name-set computation
(and the `dimindex(:'a) - 1 = wordBits - 1` identification) is tracked
separately; the recursion itself is bridged here.
-/

namespace Flapjack.RiscV.CakeAlloc

open Flapjack.Compiler.Backend.WordToStack

/-- `(x <<< 1) &&& 1 = 0` for the core Nat-shift `BitVec` instance.  The explicit
`(1 : Nat)` shift amount is required because importing `Flapjack.RiscV.Model`
(via `RegisterMap`/`CakeAllocatorCore`) installs a competing `ShiftLeft` instance
whose shift amount is a `BitVec`, which is syntactically distinct from the core
lemma's form. -/
theorem and_one_shift {w : Nat} [NeZero w] (x : BitVec w) :
    (x <<< (1 : Nat)) &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  have hw : 0 < w := Nat.pos_of_ne_zero (NeZero.ne w)
  cases i with
  | zero => simp [hw]
  | succ j => simp [Nat.succ_lt_succ_iff]

theorem shiftLeft_or_one {w : Nat} [NeZero w] (x : BitVec w) :
    x <<< (1 : Nat) ||| 1 = x <<< (1 : Nat) + 1 :=
  (BitVec.add_eq_or_of_and_eq_zero (x <<< (1 : Nat)) 1 (and_one_shift x)).symm

theorem ofNat_shift {w : Nat} [NeZero w] (n : Nat) :
    BitVec.ofNat w (n * 2) = (BitVec.ofNat w n) <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.pow_one]
  rw [Nat.mod_mul_mod]

theorem ofNat_shift_or_one {w : Nat} [NeZero w] (n : Nat) :
    BitVec.ofNat w (n * 2 + 1) = (BitVec.ofNat w n) <<< (1 : Nat) ||| 1 := by
  rw [BitVec.ofNat_add (n * 2) 1, ofNat_shift n, shiftLeft_or_one]
  rfl

/-- Executable `bitsToWord` agrees with the tagged `bitsToWordW` after the
carrier conversion, for arbitrary inputs (including `bits.length > width`, where
both sides truncate the high bits). -/
theorem bitsToWord_ofNat_eq {w : Nat} [NeZero w] (bits : List Bool) :
    BitVec.ofNat w (bitsToWord bits) = bitsToWordW (width := w) bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit
    · simp only [bitsToWord, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, bitsToWordW]
      rw [← ih, ofNat_shift]
    · simp only [bitsToWord, ↓reduceIte, bitsToWordW]
      rw [← ih, ofNat_shift_or_one]

/-- Fuel-indexed executable chunking maps onto `wordListW`.  `hfuel` rules out
exhausting the executable fuel before the bit list is consumed (each chunk
removes at least one bit). -/
theorem frameBitmapWordsAux_map {width : Nat} [NeZero width] (chunkSize fuel : Nat)
    (bits : List Bool) (hfuel : bits.length ≤ fuel) :
    (frameBitmapWordsAux chunkSize (fuel + 1) bits).map (BitVec.ofNat width) =
      wordListW (width := width) bits chunkSize := by
  induction fuel generalizing bits with
  | zero =>
    have hnil : bits = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hfuel)
    subst hnil
    rw [frameBitmapWordsAux, wordListW]
    rw [if_pos (by simp), if_pos (by simp)]
    simp only [List.map_cons, List.map_nil, bitsToWord_ofNat_eq]
  | succ fuel ih =>
    rw [frameBitmapWordsAux, wordListW]
    by_cases h : bits.length ≤ chunkSize ∨ chunkSize = 0
    · have hb : (chunkSize = 0 || bits.length ≤ chunkSize) = true := by
        rw [Bool.or_eq_true]; rcases h with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inl (by simp [h])
      rw [if_pos (by simp [hb]), if_pos h]
      simp only [List.map_cons, List.map_nil, bitsToWord_ofNat_eq]
    · have hb : (chunkSize = 0 || bits.length ≤ chunkSize) = false := by
        rw [Bool.or_eq_false_iff]
        refine ⟨?_, ?_⟩
        · simp only [decide_eq_false_iff_not]; exact fun hh => h (Or.inr hh)
        · simp only [decide_eq_false_iff_not]; exact fun hh => h (Or.inl hh)
      rw [if_neg (by simp [hb]), if_neg h]
      simp only [List.map_cons, bitsToWord_ofNat_eq]
      have hlt : (bits.drop chunkSize).length ≤ fuel := by
        have h1 : (bits.drop chunkSize).length = bits.length - chunkSize := List.length_drop
        omega
      rw [ih (bits.drop chunkSize) hlt]

/-- Executable `frameBitmapWords` maps onto `wordListW`. -/
theorem frameBitmapWords_map {width : Nat} [NeZero width] (chunkSize : Nat)
    (bits : List Bool) :
    (frameBitmapWords chunkSize bits).map (BitVec.ofNat width) =
      wordListW (width := width) bits chunkSize := by
  rw [frameBitmapWords]
  exact frameBitmapWordsAux_map chunkSize bits.length bits (Nat.le_refl _)

/-- Executable `writeBitmap`'s bitmap-word recursion maps onto `wordListW` for the
bitmap it constructs.  The name-set construction (`names`) is the documented
remaining mismatch and is left as-is. -/
theorem writeBitmap_map {width : Nat} [NeZero width] (live : List Nat) (k f' wordBits : Nat) :
    (writeBitmap live k f' wordBits).map (BitVec.ofNat width) =
      wordListW (width := width)
        ((List.range f').map (fun slot =>
          (live.map (fun r => (f' - 1) - (r / 2 - k))).contains slot) ++ [true])
        (wordBits - 1) := by
  dsimp only [writeBitmap]
  exact frameBitmapWords_map (wordBits - 1) _

end Flapjack.RiscV.CakeAlloc