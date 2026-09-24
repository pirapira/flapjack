import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# Agreement of the source and target `byte_align` renderings

HOL `byte$byte_align_def` (`src/n-bit/alignmentScript.sml:23`) is
`byte_align (w : 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w`, i.e. the low
`LOG2 (width DIV 8)` address bits are cleared.

The source-side byte codec renders this as `panByteAlignHOL` (division and
multiplication by `2 ^ LOG2 (width / 8)`) and the target-side codec as
`riscvByteAlignHOL` (shift out and back). This module proves the two renderings
agree for every word width and address, which is the alignment half of the
source/target byte-store correspondence
(`Flapjack/Pancake/CrepToLoop/StateRel.lean`, HOL
`write_bytearray_mem_rel`). Both helpers are Flapjack-specific renderings of a
HOL standard-library formula that lives outside the CakeML submodule, so this
declaration carries no `@[hol]` tag.
-/

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

end Flapjack
