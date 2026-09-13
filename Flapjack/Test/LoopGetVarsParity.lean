import Flapjack.LoopSemantics

/-!
# Original-domain parity for `get_vars` / `loopReadLocals`

`Flapjack.loopReadLocals` (Flapjack/LoopSemantics.lean:118) is the Lean
counterpart of the original Pancake `get_vars` definition:

```
cakeml/pancake/semantics/loopSemScript.sml:98-106 (get_vars_def)
```

The expected values below are transcribed from the checked-in HOL EVAL probe
output `scripts/hol-probes/loop_sem_get_vars_probe.out`, produced by
`scripts/hol-probes/loop_sem_get_vars_probeScript.sml`.  Regenerate with:

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

The probe evaluates `get_vars` against a `word_loc` map; the Lean test uses the
structural `ProbeWordLoc` mirror so that both `Word` and `Loc` locals are
compared.  Only the observed result is compared; the sptree representation is
an implementation detail of the original state.
-/

namespace Flapjack.Test.LoopGetVarsParity

open Flapjack

/-- Structural mirror of the original `word_loc` constructors that `get_vars`
    can observe. -/
inductive ProbeWordLoc where
  | word (value : Nat)
  | loc (identifier offset : Nat)
deriving DecidableEq, Repr

/-- Transcribed from `get_vars_hit=SOME [Word 5w; Word 7w]`. -/
def originalHit : Option (List ProbeWordLoc) :=
  some [.word 5, .word 7]

/-- Transcribed from `get_vars_miss=NONE`. -/
def originalMiss : Option (List ProbeWordLoc) :=
  none

/-- Transcribed from `get_vars_empty=SOME []`. -/
def originalEmpty : Option (List ProbeWordLoc) :=
  some []

/-- Transcribed from `get_vars_order=SOME [Word 7w; Word 5w]`. -/
def originalOrder : Option (List ProbeWordLoc) :=
  some [.word 7, .word 5]

/-- Transcribed from `get_vars_loc=SOME [Loc 9 0]`. -/
def originalLoc : Option (List ProbeWordLoc) :=
  some [.loc 9 0]

def twoWords : Nat → Option ProbeWordLoc
  | 1 => some (.word 5)
  | 2 => some (.word 7)
  | _ => none

def oneWord : Nat → Option ProbeWordLoc
  | 1 => some (.word 5)
  | _ => none

def oneLoc : Nat → Option ProbeWordLoc
  | 1 => some (.loc 9 0)
  | _ => none

#guard loopReadLocals twoWords [1, 2] == originalHit
#guard loopReadLocals oneWord [1, 3] == originalMiss
#guard loopReadLocals oneWord [] == originalEmpty
#guard loopReadLocals twoWords [2, 1] == originalOrder
#guard loopReadLocals oneLoc [1] == originalLoc

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop get_vars hit order", loopReadLocals twoWords [1, 2] == originalHit),
      ("Loop get_vars missing local", loopReadLocals oneWord [1, 3] == originalMiss),
      ("Loop get_vars empty list", loopReadLocals oneWord [] == originalEmpty),
      ("Loop get_vars preserves request order",
        loopReadLocals twoWords [2, 1] == originalOrder),
      ("Loop get_vars non-word local", loopReadLocals oneLoc [1] == originalLoc) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopGetVarsParity
