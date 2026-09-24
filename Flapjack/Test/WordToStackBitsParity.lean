import Flapjack.Compiler.Backend.WordToStack
import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.CakeAllocatorBitsBridge

/-!
# Word-to-Stack `bits_to_word` / `word_list` parity

Parity fixture for `Flapjack.Compiler.Backend.WordToStack.bitsToWordW` and
`wordListW`, the width-indexed faithful counterparts of HOL
`bits_to_word_def`/`word_list_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:225,231`) tagged in bead
`flapjack-pxn.18.5.15.3.1`.

The expected rows are the direct HOL `EVAL` results checked in at
`scripts/hol-probes/word_to_stack_bits_to_word_probe.out`:

```
bits_empty=0w  bits_true=1w  bits_false=0w
bits_true_false_true=5w  bits_all_true_3=7w  bits_pattern=18w
bits_overflow_65=0xFFFFFFFFFFFFFFFFw  wordlist_short=[1w]
wordlist_chunk=[7w; 7w; 1w]
```

The examples also tie the faithful words back to the untagged executable
`Flapjack.RiscV.CakeAlloc` `bitsToWord`/`frameBitmapWords`, via the untagged
bridge lemmas in `Flapjack.RiscV.CakeAllocatorBitsBridge` (`bitsToWord_ofNat_eq`,
`frameBitmapWords_map`).  `bits_overflow_65` documents the out-of-range boundary:
inputs longer than the word width wrap on both sides.
-/

namespace Flapjack.Test.WordToStackBitsParity

open Flapjack.Compiler.Backend.WordToStack

def parityGuard : Bool :=
  (bitsToWordW (width := 64) ([] : List Bool) == 0) &&
  (bitsToWordW (width := 64) [true] == 1) &&
  (bitsToWordW (width := 64) [false] == 0) &&
  (bitsToWordW (width := 64) [true, false, true] == 5) &&
  (bitsToWordW (width := 64) [true, true, true] == 7) &&
  (bitsToWordW (width := 64) [false, true, false, false, true] == 18) &&
  (bitsToWordW (width := 64) (List.replicate 65 true) == 0xFFFFFFFFFFFFFFFF) &&
  (wordListW (width := 64) [true, false] 4 == [1]) &&
  (wordListW (width := 64) [true, true, true, true, true] 2 == [7, 7, 1]) &&
  ((Flapjack.RiscV.CakeAlloc.frameBitmapWords 4 [true, false]).map (BitVec.ofNat 64) ==
    wordListW (width := 64) [true, false] 4) &&
  (BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord (List.replicate 65 true)) ==
    bitsToWordW (width := 64) (List.replicate 65 true))

#eval parityGuard
#guard parityGuard

example : bitsToWordW (width := 64) [true, false, true] = (5 : BitVec 64) := by decide

example : (bitsToWordW (width := 8) [true, false, true]).toNat =
    Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true] := by decide

/-- Arbitrary-input executable/tagged equivalence (stronger than in-range). -/
example : BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord [false, true, true, false]) =
    bitsToWordW (width := 64) [false, true, true, false] :=
  Flapjack.RiscV.CakeAlloc.bitsToWord_ofNat_eq _

/-- The executable chunking maps onto the tagged `wordListW`. -/
example : (Flapjack.RiscV.CakeAlloc.frameBitmapWords 2
      [true, true, true, true, true]).map (BitVec.ofNat 64) =
    wordListW (width := 64) [true, true, true, true, true] 2 :=
  Flapjack.RiscV.CakeAlloc.frameBitmapWords_map 2 _

def runChecks : IO Bool := do
  IO.println "PASS Word-to-Stack bits_to_word/word_list oracle rows"
  IO.println "PASS executable bitsToWord/frameBitmapWords map to tagged recursion"
  pure parityGuard

end Flapjack.Test.WordToStackBitsParity