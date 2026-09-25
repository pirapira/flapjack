import Flapjack.Pancake.Proofs.CrepArith

namespace Flapjack.Test.CrepeDest2ExpParity

open Flapjack.RiscV

/-! Direct parity for `crep_arith$dest_2exp_def`
    (`crep_arithScript.sml:15`). -/
def word (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

@[instance_reducible] def finiteWordDimension8 : HolFiniteDimension (Fin 8) :=
  inferInstance

def finiteWord8 (value : Nat) : Fin 8 → Bool :=
  bitVecToHolWord finiteWordDimension8 (word value)

def canonicalWordBits8 (value : Nat) : Fin 8 → Bool :=
  bitVecToHolWordBits (word value)

def parityGuard : Bool :=
  crepDest2Exp 0 (word 0) == none &&
  crepDest2Exp 3 (word 1) == some 3 &&
  crepDest2Exp 0 (word 1) == some 0 &&
  crepDest2Exp 0 (word 2) == some 1 &&
  crepDest2Exp 4 (word 4) == some 6 &&
  crepDest2Exp 0 (word 4) == some 2 &&
  crepDest2Exp 0 (word 8) == some 3 &&
  crepDest2Exp 0 (word 3) == none &&
  crepDest2Exp 0 (word 6) == none &&
  crepDest2Exp 0 (word 255) == none

#eval parityGuard
#guard parityGuard

/-! The bounded production helper agrees with the unbounded recursive spec
    on every direct HOL-EVAL row above, including the rejected odd values and
    the width-boundary all-ones value. The theorem is generic in the BitVec
    width; these observations keep the fixture tied to the direct HOL rows. -/
def recursiveSpecParity : Bool :=
  (crepDest2Exp 0 (word 0) == crepDest2ExpBitVecSpec 0 (word 0)) &&
  (crepDest2Exp 3 (word 1) == crepDest2ExpBitVecSpec 3 (word 1)) &&
  (crepDest2Exp 0 (word 1) == crepDest2ExpBitVecSpec 0 (word 1)) &&
  (crepDest2Exp 0 (word 2) == crepDest2ExpBitVecSpec 0 (word 2)) &&
  (crepDest2Exp 4 (word 4) == crepDest2ExpBitVecSpec 4 (word 4)) &&
  (crepDest2Exp 0 (word 4) == crepDest2ExpBitVecSpec 0 (word 4)) &&
  (crepDest2Exp 0 (word 8) == crepDest2ExpBitVecSpec 0 (word 8)) &&
  (crepDest2Exp 0 (word 3) == crepDest2ExpBitVecSpec 0 (word 3)) &&
  (crepDest2Exp 0 (word 6) == crepDest2ExpBitVecSpec 0 (word 6)) &&
  (crepDest2Exp 0 (word 255) == crepDest2ExpBitVecSpec 0 (word 255))

#eval recursiveSpecParity
#guard recursiveSpecParity

/-! These are the three successful input/exponent rows also recorded by the
    direct HOL destination-recognizer probe above. They exercise the wrapped
    `BitVec.ofNat` image of HOL `word_log2` on the same width-8 inputs. -/
def boundParity : Bool :=
  (3 : Nat) ≤ 3 + (BitVec.ofNat 8 (Nat.log2 (word 1).toNat)).toNat &&
  (6 : Nat) ≤ 4 + (BitVec.ofNat 8 (Nat.log2 (word 4).toNat)).toNat &&
  (3 : Nat) ≤ 0 + (BitVec.ofNat 8 (Nat.log2 (word 8).toNat)).toNat

#eval boundParity
#guard boundParity

example : word 1 = BitVec.shiftLeft (1 : RiscV.Word 8) 0 :=
  crepDest2Exp_eq_shift (word 1) 0 (by native_decide)

example : word 2 = BitVec.shiftLeft (1 : RiscV.Word 8) 1 :=
  crepDest2Exp_eq_shift (word 2) 1 (by native_decide)

example : word 8 = BitVec.shiftLeft (1 : RiscV.Word 8) 3 :=
  crepDest2Exp_eq_shift (word 8) 3 (by native_decide)

/-! These canonical finite-index rows check the all-width support theorem on
    the same successful `8w` and highest-bit (`128w`) shifts printed by the
    direct HOL probe. -/
example : canonicalWordBits8 8 =
    bitVecToHolWordBits (BitVec.shiftLeft (1 : BitVec 8) 3) :=
  crepDest2ExpHolWordBits_eq_lsl_support (canonicalWordBits8 8) 3
    (by decide +kernel)

example : canonicalWordBits8 128 =
    bitVecToHolWordBits (BitVec.shiftLeft (1 : BitVec 8) 7) :=
  crepDest2ExpHolWordBits_eq_lsl_support (canonicalWordBits8 128) 7
    (by decide +kernel)

example : 3 < 8 :=
  crepDest2Exp_lt_width (word 8) 3 (by native_decide)

example : 3 ≤ 0 + (BitVec.ofNat 8 (Nat.log2 (word 8).toNat)).toNat :=
  crepDest2ExpBound 0 (word 8) 3
    (by decide +kernel)

example : 6 ≤ 4 + (BitVec.ofNat 8 (Nat.log2 (word 4).toNat)).toNat :=
  crepDest2ExpBound 4 (word 4) 6
    (by decide +kernel)

example : 6 ≤ 4 + (holWordToBitVec finiteWordDimension8
    (bitVecToHolWord finiteWordDimension8
      (BitVec.ofNat 8 (Nat.log2
        (holWordToBitVec finiteWordDimension8 (finiteWord8 4)).toNat)))).toNat :=
  crepDest2ExpHolFiniteDimensionBoundSupport finiteWordDimension8 4
    (finiteWord8 4) 6 (by decide +kernel)

example : 3 ≤ 3 + (holWordToBitVec finiteWordDimension8
    (bitVecToHolWord finiteWordDimension8
      (BitVec.ofNat 8 (Nat.log2
        (holWordToBitVec finiteWordDimension8 (finiteWord8 1)).toNat)))).toNat :=
  crepDest2ExpHolFiniteDimensionBoundSupport finiteWordDimension8 3
    (finiteWord8 1) 3 (by decide +kernel)

end Flapjack.Test.CrepeDest2ExpParity
