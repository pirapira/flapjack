/-!
# Cake frame-occupancy bitmap vector oracle

Bead `flapjack-pxn.8.5.14.1.5` requires that every expected answer for the
frame-occupancy work comes from an original CakeML run or a checked Cake
artifact, never a hand-entered Flapjack expectation.

The vectors below are the verbatim `cake_bitmaps:` `.quad` payloads of the
checked `NAME.cake.S` artifacts under
`scripts/parity-difffuzz-findings/frame-occupancy/`, obtained with

  grep -m1 -E '^\s*\.quad ' scripts/parity-difffuzz-findings/frame-occupancy/NAME.cake.S

The original encoding is: word 0 is the literal header `4`; every later word
is `2 ^ f'`, where `f'` is the caller's frame size (in words) minus the
bitmap slot, one word per non-tail call continuation.

`fixtureFprimes` records `f'` for each continuation (documented in the
fixture `README.md`) and `cakeFrameVectorFromFprime` re-derives the artifact
vector from it, so the equation

  cakeFrameVectorFromFprime (fixtureFprimes) = (checked cake_bitmaps payload)

is what this module pins.
-/

namespace Flapjack.Test.CakeFrameVectorParity

/-- Cake's bitmap vector: a literal header word `4`, then `2 ^ f'` per call
continuation (`word_to_stackScript.sml` `init_bitmaps` / `write_bitmap`). -/
def cakeFrameVectorFromFprime (fprimes : List Nat) : List Nat :=
  4 :: fprimes.map (fun fprime => 2 ^ fprime)

/-- Checked fixture vectors: `(name, f' per continuation, cake_bitmaps .quad)`.
The second component is the `README.md` frame-size table; the third is the
verbatim artifact payload. -/
def fixtures : List (String × List Nat × List Nat) :=
  [ ("p1", [1], [4, 2]),
    ("p2", [2], [4, 4]),
    ("p3", [2], [4, 4]),
    ("p4", [2], [4, 4]),
    ("p5", [2], [4, 4]),
    ("p6", [2, 2], [4, 4, 4]),
    ("p7", [2, 2], [4, 4, 4]),
    ("p9", [3, 3], [4, 8, 8]),
    ("p10", [4, 4], [4, 16, 16]),
    ("p11", [2, 2], [4, 4, 4]),
    ("bm_min2", [3, 3], [4, 8, 8]),
    ("live1", [2, 2], [4, 4, 4]),
    ("live3", [4, 4, 4, 4], [4, 16, 16, 16, 16]),
    ("wide", [3, 3], [4, 8, 8]),
    ("bc", [1, 1], [4, 2, 2]),
    ("bitmap_calls", [1, 1], [4, 2, 2]) ]

/-- Every checked artifact vector is exactly the Cake encoding of its
documented per-continuation frame sizes. -/
def vectorsMatchEncoding : Bool :=
  fixtures.all (fun fixture =>
    cakeFrameVectorFromFprime fixture.2.1 == fixture.2.2)

/-- The recursion fixtures (`bc`, `bitmap_calls`) have a trivial frame, so
their continuation word is `2 ^ 1 = 2`. -/
def trivialFrameWordMatches : Bool :=
  cakeFrameVectorFromFprime [1, 1] == [4, 2, 2]

/-- The multi-word fixtures widen the continuation word to `2 ^ f'`: `p9` and
`bm_min2` emit `[4, 8, 8]` and `live3` emits `[4, 16, 16, 16, 16]`. -/
def wideFrameWordsMatch : Bool :=
  cakeFrameVectorFromFprime [3, 3] == [4, 8, 8] &&
    cakeFrameVectorFromFprime [4, 4, 4, 4] == [4, 16, 16, 16, 16]

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("checked frame-occupancy vectors match the Cake 2^f' encoding",
        vectorsMatchEncoding),
      ("trivial-frame fixtures encode their continuation as 2^1",
        trivialFrameWordMatches),
      ("wide-frame fixtures encode their continuations as 2^f'",
        wideFrameWordsMatch) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeFrameVectorParity