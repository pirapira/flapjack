import Flapjack.HolRef

/-!
# Faithful Cake Word-to-Stack bitmap helpers

Lean counterpart of `cakeml/compiler/backend/word_to_stackScript.sml`, the
Word-to-Stack pass of the CakeML RISC-V backend.  This module currently ports
the pure bitmap prerequisite `bits_to_word`, which the pass uses to build the
GC/liveness bitmaps consumed by `compile_word_to_stack` and, eventually, by the
Word-to-Stack `compile_semantics` theorem
(`word_to_stackProofScript.sml:10709`).

HOL's `bits_to_word` is polymorphic over the word carrier (`'a word`) and has
no typeclass side conditions.  Following the established repository standard
(`loadShapeBytes` vs the tagged `loadShapeBytesW`; `compileExpHOL` vs the tagged
`compileExpHOLW`), the faithful interface fixes the carrier to `BitVec width`
with `[NeZero width]`.  The fixed-width, `Nat`-valued
`Flapjack.RiscV.CakeAlloc.bitsToWord` is the executable Flapjack
implementation and stays untagged.
-/

namespace Flapjack.Compiler.Backend.WordToStack

/-- Exact port of HOL `bits_to_word_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:225`):

```
(bits_to_word [] = 0w) /\
(bits_to_word (T::xs) = (bits_to_word xs << 1 || 1w)) /\
(bits_to_word (F::xs) = (bits_to_word xs << 1))
```

HOL builds the word from the head of the list, shifting each already-processed
suffix left and injecting the current bit.  `[NeZero width]` is HOL's implicit
nonempty word carrier (`'a word` has `dimindex (:'a) >= 1`); `1w` and `0w` are
HOL words of the same width as the result. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "bits_to_word_def"]
def bitsToWordW {width : Nat} [NeZero width] : List Bool → BitVec width
  | [] => 0
  | true :: bits => (bitsToWordW bits) <<< 1 ||| 1
  | false :: bits => (bitsToWordW bits) <<< 1

/-- Exact port of HOL `word_list_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:231`):

```
word_list (xs:bool list) d =
  if LENGTH xs <= d \/ (d = 0) then
    [bits_to_word xs]
  else
    bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d
```

Each emitted word packs up to `d` bits, with an explicit terminator `T`
appended so the highest set bit inside a chunk marks the chunk boundary.
The carrier and `[NeZero width]` follow the same convention as
`bitsToWordW`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "word_list_def"]
def wordListW {width : Nat} [NeZero width] (bits : List Bool) (chunkSize : Nat) :
    List (BitVec width) :=
  if bits.length ≤ chunkSize ∨ chunkSize = 0 then
    [bitsToWordW (width := width) bits]
  else
    bitsToWordW (width := width) (bits.take chunkSize ++ [true]) ::
      wordListW (bits.drop chunkSize) chunkSize
  termination_by bits.length
  decreasing_by
    simp only [List.length_drop]
    omega

end Flapjack.Compiler.Backend.WordToStack
