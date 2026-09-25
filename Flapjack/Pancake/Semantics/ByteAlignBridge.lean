import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanSemStateEval

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

end Flapjack
