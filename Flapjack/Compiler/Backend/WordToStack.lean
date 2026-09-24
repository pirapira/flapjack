import Flapjack.HolRef
import Flapjack.Misc.AppList

/-!
# Faithful Cake Word-to-Stack bitmap helpers

Lean counterpart of `cakeml/compiler/backend/word_to_stackScript.sml`, the
Word-to-Stack pass of the CakeML RISC-V backend.  This module currently ports
the pure bitmap prerequisites `bits_to_word`, `word_list`, `chunk_to_bits`,
`chunk_to_bitmap`, `const_words_to_bitmap` and `insert_bitmap`, which the pass
uses to build the
GC/liveness bitmaps consumed by `compile_word_to_stack`, together with the pure
stack-slot arithmetic helpers `num_stack_ret`, `skip_free`, `stack_arg_count`
and `stack_free` used by the return/argument path of `comp`; eventually these
feed the Word-to-Stack `compile_semantics` theorem
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

/-- Order-insensitive Lean model of HOL `write_bitmap_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:240`):

```
(write_bitmap live k f'):'a word list =
  let names = MAP (\(r,y). (f' - 1) - (r DIV 2 - k)) (toAList live) in
    word_list (GENLIST (\x. MEM x names) f' ++ [T]) (dimindex (:'a) - 1)
```

UNTAGGED.  HOL's `live` is a `num_set` (`unit spt`), whose finite-map carrier
and `toAList` ordering live in `HOL/src/finite_maps/sptreeScript.sml`, outside
the CakeML tree: `scripts/check-hol-refs.py` rejects `@[hol]` paths that are not
under `cakeml/`, and `docs/NUM-SET-AUDIT.md` models `num_set` as an
order-insensitive domain because the passes observe `toAList` only through
`MEM`/`EVERY`.  `write_bitmap` reads `toAList live` only through `MEM` of the
mapped names, so its value depends solely on the domain of `live`; this model
takes that domain directly as a `List Nat`.  The kernel-checked
`writeBitmapHOL_domain_insensitive` records exactly that insensitivity.  This is
a documented carrier mismatch, not an exact port: the definition is deliberately
**not** marked `@[hol]`.

The direct HOL `EVAL` evidence is checked in at
`scripts/hol-probes/word_to_stack_write_bitmap_probe.out`; the Lean parity
fixture is `Flapjack.Test.WordToStackBitsParity`. -/
def writeBitmapHOL {width : Nat} [NeZero width]
    (live : List Nat) (k f' : Nat) : List (BitVec width) :=
  let names := live.map (fun r => (f' - 1) - (r / 2 - k))
  wordListW ((List.range f').map (fun x => decide (x ∈ names)) ++ [true]) (width - 1)

/-- `writeBitmapHOL` depends only on the domain of `live`: any two lists with the
    same membership define the same bitmap.  This is the observable half of the
    HOL `num_set`/`toAList` carrier that `write_bitmap` uses. -/
theorem writeBitmapHOL_domain_insensitive {width : Nat} [NeZero width]
    (live₁ live₂ : List Nat) (k f' : Nat)
    (h : ∀ r, r ∈ live₁ ↔ r ∈ live₂) :
    writeBitmapHOL (width := width) live₁ k f' =
      writeBitmapHOL (width := width) live₂ k f' := by
  have hmap : ∀ x, x ∈ live₁.map (fun r => (f' - 1) - (r / 2 - k)) ↔
      x ∈ live₂.map (fun r => (f' - 1) - (r / 2 - k)) := by
    intro x
    simp only [List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, (h r).mp hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, (h r).mpr hr, rfl⟩
  have hlist : (List.range f').map
        (fun x => decide (x ∈ live₁.map (fun r => (f' - 1) - (r / 2 - k)))) =
      (List.range f').map
        (fun x => decide (x ∈ live₂.map (fun r => (f' - 1) - (r / 2 - k)))) := by
    apply List.map_congr_left
    intro x _
    exact decide_eq_decide.mpr (hmap x)
  simp only [writeBitmapHOL]
  rw [hlist]

/-- HOL `insert_bitmap_def` (`word_to_stackScript.sml:246`):
    `insert_bitmap ws (data,data_len) = let l = LENGTH ws in
       ((Append data (List ws), data_len + l), data_len)`.

    `insert_bitmap` threads the `app_list`/`num` pair built by `write_bitmap`
    (`:256`) and is used by the `comp` `StoreConsts` clause (`:532`).

    HOL is fully polymorphic in the word element type `'a`, and `insert_bitmap`
    uses no word operation (`Append`/`List` are the `misc$app_list`
    constructors; `LENGTH`/`+` are list/nat), so there is no `dimindex(:'a)` to
    specialise and the generic-`α` port below is the exact HOL body.  This is
    the same carrier choice as the reviewed `app_list`/`append_aux`/`append`
    tags in `Flapjack.Misc.AppList`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "insert_bitmap_def"]
def insertBitmap {α : Type} (ws : List α) (bitmaps : AppList α × Nat) :
    (AppList α × Nat) × Nat :=
  let l := ws.length
  ((AppList.append bitmaps.1 (AppList.list ws), bitmaps.2 + l), bitmaps.2)

/-- Exact port of HOL `num_stack_ret_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:417`):

```
num_stack_ret k vs = LENGTH vs + 1 - k
```

    Number of stack slots holding the multi-arg return value.  HOL is
    polymorphic in the value type (`vs` is only measured by `LENGTH`, which is
    the list length), and the subtraction is HOL `num` truncation, exactly
    Lean `Nat` subtraction, so the generic-`α` body below is the exact HOL
    statement with no side condition. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "num_stack_ret_def"]
def numStackRet {α : Type} (k : Nat) (vs : List α) : Nat := vs.length + 1 - k

/-- Exact port of HOL `skip_free_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:423`):

```
skip_free (k,f,f') vs = f - num_stack_ret k vs
```

    Number of slots the callee frees.  The `(k,f,f')` is a HOL `num # num # num`
    triple; `f'` is unused here, matching HOL.  Pure `num` arithmetic, so the
    generic-`α` body is exact. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "skip_free_def"]
def skipFree {α : Type} (k f _f' : Nat) (vs : List α) : Nat := f - numStackRet k vs

/-- Exact port of HOL `stack_arg_count_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:274`):

```
stack_arg_count dest arg_count k =
  case dest of
  | INL _ => (arg_count - k:num)
  | INR _ => ((arg_count - 1) - k:num)
```

    HOL's `dest` is a `('a, 'b) sum` (the call-target position or register);
    only the constructor is inspected.  The faithful Lean carrier is
    `Sum α β` with the same two `num` results, so the generic body is exact. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stack_arg_count_def"]
def stackArgCount {α β : Type} (dest : Sum α β) (arg_count k : Nat) : Nat :=
  match dest with
  | .inl _ => arg_count - k
  | .inr _ => (arg_count - 1) - k

/-- Exact port of HOL `stack_free_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:281`):

```
stack_free dest arg_count (k,f,f') = f - stack_arg_count dest arg_count k
```

    Pure `num` arithmetic on top of `stackArgCount`; `f'` is unused, matching
    HOL.  Generic in the `sum` carriers, so exact with no side condition. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stack_free_def"]
def stackFree {α β : Type} (dest : Sum α β) (arg_count k f _f' : Nat) : Nat :=
  f - stackArgCount dest arg_count k

end Flapjack.Compiler.Backend.WordToStack
