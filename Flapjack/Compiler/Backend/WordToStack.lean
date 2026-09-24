import Flapjack.HolRef

/-!
# Faithful Cake Word-to-Stack bitmap helpers

Lean counterpart of `cakeml/compiler/backend/word_to_stackScript.sml`, the
Word-to-Stack pass of the CakeML RISC-V backend.  This module currently ports
the pure bitmap prerequisites `bits_to_word`, `word_list`, `chunk_to_bits`,
`chunk_to_bitmap` and `const_words_to_bitmap`, which the pass uses to build the
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
  if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs]
  else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d
```

HOL terminates by `measure (LENGTH o FST)`: the recursive argument is
`DROP d xs`, strictly shorter whenever the `else` branch is taken.  As with
`bitsToWordW`, the faithful carrier is `BitVec width` with `[NeZero width]`
(HOL's `'a word`); a zero-length chunk still emits one word (`0w` via
`bitsToWordW []`). -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "word_list_def"]
def wordListW {width : Nat} [NeZero width] (xs : List Bool) (d : Nat) : List (BitVec width) :=
  if xs.length ≤ d ∨ d = 0 then [bitsToWordW xs]
  else bitsToWordW (xs.take d ++ [true]) :: wordListW (xs.drop d) d
termination_by xs.length
decreasing_by
  simp only [List.length_drop]
  omega

/-- Exact port of HOL `chunk_to_bits_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:386`):

```
chunk_to_bits ([]:(bool # 'a word) list) = 1w
chunk_to_bits ((b,w)::ws) =
  let res = (chunk_to_bits ws) << 1 in
    if b then res + 1w else res
```

HOL is polymorphic over the word carrier and ignores the word payload `w`;
only the boolean tag contributes.  The faithful carrier is `BitVec width` with
`[NeZero width]` (HOL's `'a word`). -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "chunk_to_bits_def"]
def chunkToBitsW {width : Nat} [NeZero width] : List (Bool × BitVec width) → BitVec width
  | [] => 1
  | (b, _) :: ws =>
    let res := (chunkToBitsW ws) <<< 1
    if b then res + 1 else res

/-- Exact port of HOL `chunk_to_bitmap_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:393`):

```
chunk_to_bitmap ws = chunk_to_bits ws :: MAP SND ws
```

The word chunk formed by `chunkToBitsW` is prepended to the payload words of the
chunks.  HOL is polymorphic over the word carrier; the faithful carrier is
`BitVec width` with `[NeZero width]` (HOL's `'a word`). -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "chunk_to_bitmap_def"]
def chunkToBitmapW {width : Nat} [NeZero width]
    (ws : List (Bool × BitVec width)) : List (BitVec width) :=
  chunkToBitsW ws :: ws.map Prod.snd

/-- Exact port of HOL `const_words_to_bitmap_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:397`):

```
const_words_to_bitmap (ws:(bool # 'a word) list) (ws_len:num) =
  if ws_len < (dimindex (:'a) - 1) \/ (dimindex (:'a) - 1) = 0
  then chunk_to_bitmap ws
  else
    let h = TAKE (dimindex (:'a) - 1) ws in
    let t = DROP (dimindex (:'a) - 1) ws in
      chunk_to_bitmap h ++ const_words_to_bitmap t (ws_len - (dimindex (:'a) - 1))
```

HOL is polymorphic over the word carrier, whose bit width is
`dimindex (:'a)`; the faithful Lean carrier is `BitVec width` with
`[NeZero width]`, so `width` plays the role of `dimindex (:'a)`.  The boundary
is HOL's strict `<` together with the `dimindex (:'a) - 1 = 0` escape, both kept
verbatim.  HOL terminates because `DROP` removes `dimindex (:'a) - 1 >= 1`
elements in the `else` branch. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "const_words_to_bitmap_def"]
def constWordsToBitmapW {width : Nat} [NeZero width]
    (ws : List (Bool × BitVec width)) (ws_len : Nat) : List (BitVec width) :=
  if ws_len < width - 1 ∨ width - 1 = 0 then chunkToBitmapW ws
  else
    let h := ws.take (width - 1)
    let t := ws.drop (width - 1)
    chunkToBitmapW h ++ constWordsToBitmapW t (ws_len - (width - 1))
termination_by ws_len
decreasing_by omega

end Flapjack.Compiler.Backend.WordToStack
