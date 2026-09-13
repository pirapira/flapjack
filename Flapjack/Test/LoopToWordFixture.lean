/-!
# Original-derived fixture for the LoopToWord port

Expected values produced by the original CakeML Pancake definitions with HOL4
`EVAL`, not by a second Lean implementation:

* `find_var` — `cakeml/pancake/loop_to_wordScript.sml:10`
* `find_reg_imm` — `cakeml/pancake/loop_to_wordScript.sml:17`
* `make_ctxt` — `cakeml/pancake/loop_to_wordScript.sml:152`

Regenerate with `scripts/probe-loop-to-word.sml` (HOL4 + CakeML on the load
path), then transcribe the printed values below:

```
cd <cakeml>/pancake && Holmake loop_to_wordTheory
<hol> < /path/to/flapjack/scripts/probe-loop-to-word.sml
```

HOL4 is not available in the environment where this fixture was added, so the
literals below were transcribed from the definitions and the probe above must
be run to validate them before the parity beads are closed.
-/

namespace Flapjack.Test.LoopToWordFixture

/-- `find_var` on explicit finite maps: (context, key, result). -/
def findVarCases : List (List (Nat × Nat) × Nat × Nat) :=
  [ ([], 0, 0)
  , ([], 99, 0)
  , ([(3, 7)], 3, 7)
  , ([(3, 7)], 4, 0)
  ]

/-- `find_var` over `make_ctxt`: (next, variables, key, result). -/
def makeCtxtCases : List (Nat × List Nat × Nat × Nat) :=
  [ (2, [10, 11, 12], 10, 2)
  , (2, [10, 11, 12], 11, 4)
  , (2, [10, 11, 12], 12, 6)
  , (2, [10, 11, 12], 99, 0)
  , (4, [1, 2], 1, 4)
  , (4, [1, 2], 2, 6)
  , (4, [1, 2], 9, 0)
  ]

/-- `find_reg_imm` register case: (context, name, result). -/
def findRegImmRegCases : List (List (Nat × Nat) × Nat × Nat) :=
  [ ([], 11, 0)
  , ([(11, 4)], 11, 4)
  ]

/-- `find_reg_imm` immediate case leaves the immediate unchanged. -/
def findRegImmImmCases : List Nat := [0, 5, 99]

end Flapjack.Test.LoopToWordFixture
