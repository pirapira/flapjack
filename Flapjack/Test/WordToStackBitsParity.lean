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
    ([5, 3] : List (BitVec 64)) := by decide +kernel
/-! ## `chunk_to_bits` parity

Rows for the width-indexed `chunkToBitsW`, tagged against HOL
`chunk_to_bits_def` (`cakeml/compiler/backend/word_to_stackScript.sml:386`;
bead `flapjack-pxn.18.5.15.3.3`), from
`scripts/hol-probes/word_to_stack_chunk_to_bits_probe.out`:

```
cb_empty=1w  cb_single_true=3w  cb_single_false=2w
cb_true_false=5w  cb_false_true=6w  cb_three=11w  cb_ignores_word=T
```
-/

def chunkToBitsParityGuard : Bool :=
  (chunkToBitsW (width := 64) ([] : List (Bool × BitVec 64)) == 1) &&
  (chunkToBitsW (width := 64) [(true, 0)] == 3) &&
  (chunkToBitsW (width := 64) [(false, 0)] == 2) &&
  (chunkToBitsW (width := 64) [(true, 0), (false, 0)] == 5) &&
  (chunkToBitsW (width := 64) [(false, 0), (true, 0)] == 6) &&
  (chunkToBitsW (width := 64) [(true, 0), (true, 0), (false, 0)] == 11)

#eval chunkToBitsParityGuard
#guard chunkToBitsParityGuard

example : chunkToBitsW (width := 64) [(true, (0 : BitVec 64)), (false, 9)] =
    chunkToBitsW (width := 64) [(true, 0), (false, 0)] := by decide

/-! ## `chunk_to_bitmap` / `const_words_to_bitmap` parity

Rows for the width-indexed `chunkToBitmapW` and `constWordsToBitmapW`, tagged
against HOL `chunk_to_bitmap_def` / `const_words_to_bitmap_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:393,397`; bead
`flapjack-pxn.18.5.15.3.4`), from
`scripts/hol-probes/word_to_stack_chunk_to_bitmap_probe.out`:

```
cbm_empty=[1w]  cbm_two=[5w; 0w; 9w]  cbm_payload=[3w; 7w]
cwb_empty=[1w]  cwb_short=[5w; 0w; 9w]
cwb_boundary8=[213w; 1w; 2w; 3w; 4w; 5w; 6w; 7w; 1w]
cwb_split8=[213w; 1w; 2w; 3w; 4w; 5w; 6w; 7w; 2w; 8w]
```

`cwb_boundary8` exercises `word8` (`dimindex (:'a) = 8`) with
`ws_len = dimindex-1 = 7`: HOL's strict `<` still recurses, splitting off the
first seven words and appending `chunk_to_bitmap [] = [1w]`.
-/

def chunkToBitmapParityGuard : Bool :=
  (chunkToBitmapW (width := 64) ([] : List (Bool × BitVec 64)) == [1]) &&
  (chunkToBitmapW (width := 64) [(true, 0), (false, 9)] == [5, 0, 9]) &&
  (chunkToBitmapW (width := 64) [(true, 7)] == [3, 7]) &&
  (constWordsToBitmapW (width := 64) ([] : List (Bool × BitVec 64)) 0 == [1]) &&
  (constWordsToBitmapW (width := 64) [(true, 0), (false, 9)] 2 == [5, 0, 9]) &&
  (constWordsToBitmapW (width := 8)
      [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7)] 7
      == [213, 1, 2, 3, 4, 5, 6, 7, 1]) &&
  (constWordsToBitmapW (width := 8)
      [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7), (false, 8)] 8
      == [213, 1, 2, 3, 4, 5, 6, 7, 2, 8])

#eval chunkToBitmapParityGuard
#guard chunkToBitmapParityGuard

example : constWordsToBitmapW (width := 8)
    [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7), (false, 8)] 8 =
    ([213, 1, 2, 3, 4, 5, 6, 7, 2, 8] : List (BitVec 8)) := by decide +kernel

/-! ## `write_bitmap` oracle parity (untagged model)

`writeBitmapHOL` models HOL `write_bitmap_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:240`) at the domain level and
is deliberately **not** tagged: HOL's `live` is a `num_set` (`unit spt`) whose
finite-map/`toAList` carrier lives outside the CakeML tree, so the faithful
observation is the `writeBitmapHOL_domain_insensitive` theorem rather than a
matching declaration (see `docs/NUM-SET-AUDIT.md`).  Rows from the direct HOL
`EVAL` probe `scripts/hol-probes/word_to_stack_write_bitmap_probe.out`:

```
wb_empty=[16w]  wb_single=[24w]  wb_two=[24w]  wb_offset=[240w; 2w]
wb_boundary=[0xE000000000000000w; 3w]
wb_order_a=[192w; 3w]  wb_order_b=[192w; 3w]  wb_order_eq=T
```
-/

def writeBitmapParityGuard : Bool :=
  (writeBitmapHOL (width := 8) ([] : List Nat) 0 4 == [16]) &&
  (writeBitmapHOL (width := 8) [0] 0 4 == [24]) &&
  (writeBitmapHOL (width := 8) [0, 1] 0 4 == [24]) &&
  (writeBitmapHOL (width := 8) [2, 4, 6] 0 8 == [240, 2]) &&
  (writeBitmapHOL (width := 64) [0, 2, 4] 0 64 == [(0xE000000000000000 : BitVec 64), 3]) &&
  (writeBitmapHOL (width := 8) [0, 1, 2] 0 8 == [192, 3]) &&
  (writeBitmapHOL (width := 8) [2, 0, 1] 0 8 == [192, 3])

#eval writeBitmapParityGuard
#guard writeBitmapParityGuard

example : writeBitmapHOL (width := 8) [0, 1, 2] 0 8 =
    writeBitmapHOL (width := 8) [2, 0, 1] 0 8 :=
  writeBitmapHOL_domain_insensitive [0, 1, 2] [2, 0, 1] 0 8
    (by intro r; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

end Flapjack.Test.WordToStackBitsParity
