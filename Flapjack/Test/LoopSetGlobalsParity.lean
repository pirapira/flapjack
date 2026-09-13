import Flapjack.LoopSemantics

/-!
# Original-domain parity for `set_globals` / `updateLoopGlobal`

`Flapjack.updateLoopGlobal` (Flapjack/LoopSemantics.lean:114) is the Lean
counterpart of the original Pancake `set_globals` definition:

```
cakeml/pancake/semantics/loopSemScript.sml:52-55 (set_globals_def)
  set_globals gv w s = s with globals := s.globals |+ (gv,w)
```

The original state field is `globals : 5 word |-> 'a word_loc` and is read
with `FLOOKUP` (loopSemScript.sml:74), so the probe observes `FLOOKUP` after the
update.  The expected values below are transcribed from the checked-in HOL EVAL
probe output `scripts/hol-probes/loop_sem_set_globals_probe.out`, produced by
`scripts/hol-probes/loop_sem_set_globals_probeScript.sml`.  Regenerate with:

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

The homogeneous Lean counterpart models the finite map as `Nat → Option Nat`;
the probe's 5-bit word keys `3w`/`4w` are transcribed as `3`/`4` and the
stored `Word nw` values as the numeral `n`.  Only the observed lookup result is
compared, since the finite-map representation is an implementation detail of
the original state.
-/

namespace Flapjack.Test.LoopSetGlobalsParity

open Flapjack

/-- Transcribed from `set_globals_new=SOME (Word 5w)`. -/
def originalNew : Option Nat :=
  some 5

/-- Transcribed from `set_globals_overwrite=SOME (Word 5w)`. -/
def originalOverwrite : Option Nat :=
  some 5

/-- Transcribed from `set_globals_miss=NONE`. -/
def originalMiss : Option Nat :=
  none

/-- Transcribed from `set_globals_sibling=SOME (Word 1w)`. -/
def originalSibling : Option Nat :=
  some 1

def emptyGlobals : Nat → Option Nat :=
  fun _ => none

def oneGlobal : Nat → Option Nat
  | 3 => some 1
  | _ => none

def twoGlobals : Nat → Option Nat
  | 3 => some 1
  | 4 => some 7
  | _ => none

#guard updateLoopGlobal emptyGlobals 3 5 3 == originalNew
#guard updateLoopGlobal oneGlobal 3 5 3 == originalOverwrite
#guard updateLoopGlobal emptyGlobals 3 5 4 == originalMiss
#guard updateLoopGlobal twoGlobals 4 7 3 == originalSibling

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop set_globals inserts new global",
        updateLoopGlobal emptyGlobals 3 5 3 == originalNew),
      ("Loop set_globals overwrites existing global",
        updateLoopGlobal oneGlobal 3 5 3 == originalOverwrite),
      ("Loop set_globals leaves missing key absent",
        updateLoopGlobal emptyGlobals 3 5 4 == originalMiss),
      ("Loop set_globals leaves sibling global untouched",
        updateLoopGlobal twoGlobals 4 7 3 == originalSibling) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopSetGlobalsParity
