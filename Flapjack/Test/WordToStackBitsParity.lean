import Flapjack.Compiler.Backend.WordToStack
import Flapjack.RiscV.CakeAllocatorCore

/-!
# Word-to-Stack `bits_to_word` parity

Parity fixture for `Flapjack.Compiler.Backend.WordToStack.bitsToWordW`, the
width-indexed faithful counterpart of HOL `bits_to_word_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:225`) tagged in bead
`flapjack-pxn.18.5.15.3.1`.

The expected rows are the direct HOL `EVAL` results checked in at
`scripts/hol-probes/word_to_stack_bits_to_word_probe.out` (oracle checkout
`flapjack2`, `word_to_stackTheory` prebuilt):

```
bits_empty=0w  bits_true=1w  bits_false=0w
bits_true_false_true=5w  bits_all_true_3=7w  bits_pattern=18w
```

The last example ties the faithful word result back to the untagged executable
`Flapjack.RiscV.CakeAlloc.bitsToWord` for the in-range case.
-/

namespace Flapjack.Test.WordToStackBitsParity

open Flapjack.Compiler.Backend.WordToStack

def parityGuard : Bool :=
  (bitsToWordW (width := 64) ([] : List Bool) == 0) &&
  (bitsToWordW (width := 64) [true] == 1) &&
  (bitsToWordW (width := 64) [false] == 0) &&
  (bitsToWordW (width := 64) [true, false, true] == 5) &&
  (bitsToWordW (width := 64) [true, true, true] == 7) &&
  (bitsToWordW (width := 64) [false, true, false, false, true] == 18)

#eval parityGuard
#guard parityGuard

example : bitsToWordW (width := 64) [true, false, true] = (5 : BitVec 64) := by decide

example : (bitsToWordW (width := 8) [true, false, true]).toNat =
    Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true] := by decide

/-! ## `word_list` parity

Rows for the width-indexed `wordListW`, tagged against HOL `word_list_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:231`; bead
`flapjack-pxn.18.5.15.3.2`), from
`scripts/hol-probes/word_to_stack_word_list_probe.out`:

```
wl_empty_d3=[0w]  wl_empty_d0=[0w]  wl_d0=[5w]
wl_short=[5w]  wl_split=[5w; 3w]  wl_twostep=[7w; 7w; 1w]
```
-/

def wordListParityGuard : Bool :=
  (wordListW (width := 64) ([] : List Bool) 3 == [0]) &&
  (wordListW (width := 64) ([] : List Bool) 0 == [0]) &&
  (wordListW (width := 64) [true, false, true] 0 == [5]) &&
  (wordListW (width := 64) [true, false, true] 5 == [5]) &&
  (wordListW (width := 64) [true, false, true, true] 2 == [5, 3]) &&
  (wordListW (width := 64) [true, true, true, true, true] 2 == [7, 7, 1])

#eval wordListParityGuard
#guard wordListParityGuard

example : wordListW (width := 64) [true, false, true, true] 2 =
    ([5, 3] : List (BitVec 64)) := by native_decide

end Flapjack.Test.WordToStackBitsParity
