import Flapjack.RiscV.Model

/-! Signed-division corner probe for the proof-side RISC-V model.

The proof model's `.divU` instruction is the lowering target of signed loop
arithmetic and `Flapjack/RiscV/Encoding/NativeInstruction.lean` maps it to the
native `MulDiv .DIV` form (RISC-V signed `DIV`).  The original HOL equation
`dfn'DIV_def` uses `word_quot`, which truncates toward zero, so the model must
use a truncating signed quotient (`Int.tdiv` / `BitVec.sdiv`), not a Euclidean
one (`Int.ediv`).

The expected result words below are the captured outputs of the original HOL
`dfn'DIV` equation in `scripts/hol-probes/l3_divide_probe.out`, checked by
`scripts/hol-probes/check-l3-divide.py`. Regenerate the original observations
from `HOL/examples/l3-machine-code/riscv/model/riscvScript.sml` with
`HOL_PROBE_ONLY=l3_divide_probeScript.sml scripts/hol-probes/regenerate.sh`:

* `divide_value_DIV_neg7_pos2=0xFFFFFFFFFFFFFFFDw`  (`-7 / 2 = -3`)
* `divide_value_DIV_pos7_neg2=0xFFFFFFFFFFFFFFFDw`  (`7 / -2 = -3`)
* `divide_value_DIV_neg7_neg2=3w`                    (`-7 / -2 = 3`)
* `divide_value_DIV_zero_divisor=0xFFFFFFFFFFFFFFFFw` (divisor `0` -> all ones)
* `divide_value_DIV_min_neg1=0x8000000000000000w`     (`min / -1` wraps to `min`)

The Euclidean rounding previously used by the model disagrees on the first
corner (`Int.ediv (-7) 2 = -4`), which is pinned by the final example. -/
namespace Flapjack.Test.RiscVModelDivParity

open Flapjack.RiscV

/-- A 64-bit state with `x2 = a` and `x3 = b`. -/
def divState (a b : Word 64) : State 64 :=
  writeRegister (writeRegister (zeroState 64) 2 a) 3 b

example : readRegister (execute (divState (-7) 2) (.divU 5 2 3)) 5 =
    (0xFFFFFFFFFFFFFFFD : Word 64) := by
  decide

example : readRegister (execute (divState 7 (-2)) (.divU 5 2 3)) 5 =
    (0xFFFFFFFFFFFFFFFD : Word 64) := by
  decide

example : readRegister (execute (divState (-7) (-2)) (.divU 5 2 3)) 5 =
    (3 : Word 64) := by
  decide

example : readRegister (execute (divState (-7) 0) (.divU 5 2 3)) 5 =
    (0xFFFFFFFFFFFFFFFF : Word 64) := by
  decide

example : readRegister
    (execute (divState (0x8000000000000000 : Word 64) (-1)) (.divU 5 2 3)) 5 =
    (0x8000000000000000 : Word 64) := by
  decide

/-- The Euclidean rounding that the model previously used gives a different
result on this corner, documenting the corrected discrepancy. -/
example : BitVec.sdiv (-7 : Word 64) (2 : Word 64) ≠
    BitVec.ofInt 64 ((-7 : Word 64).toInt.ediv (2 : Word 64).toInt) := by
  decide

end Flapjack.Test.RiscVModelDivParity
