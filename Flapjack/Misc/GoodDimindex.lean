import Flapjack.HolRef

/-!
# Exact `good_dimindex` over the HOL word-dimension predicate

This module ports the source-library predicate `misc$good_dimindex`
(`cakeml/misc/miscScript.sml:4315`):

```
good_dimindex_def:
  good_dimindex (:'a) ⇔ dimindex (:'a) = 32 ∨ dimindex (:'a) = 64
```

The Lean word width is the HOL `dimindex (:α)`, so the Lean predicate takes a
`Nat` width and states the same disjunction. It is consumed by the byte-array
results (for example `read_write_bytearray_lemma` in
`Flapjack/Pancake/Semantics/PanProps/MemByteArray.lean`) to split a word into
the 32-bit and 64-bit cases that HOL's `set_byte_get_byte` requires.
-/

namespace Flapjack

/-- Exact port of HOL `good_dimindex` (`cakeml/misc/miscScript.sml:4315`):
    `good_dimindex (:'a) ⇔ dimindex (:'a) = 32 ∨ dimindex (:'a) = 64`. The Lean
    word width is the HOL `dimindex`, so this is the same predicate. -/
@[hol "cakeml/misc/miscScript.sml" "good_dimindex_def"]
def goodDimindex (width : Nat) : Prop := width = 32 ∨ width = 64

end Flapjack
