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

The Lean counterpart models the finite map extensionally with `BitVec 5`
keys and a `LoopWordLoc` cell wrapper, matching the source key and cell shapes.
-/

namespace Flapjack.Test.LoopSetGlobalsParity

open Flapjack

/-- Transcribed from `set_globals_new=SOME (Word 5w)`. -/
def originalNew : Option (LoopStateCell Nat) :=
  some (.word 5)

/-- Transcribed from `set_globals_overwrite=SOME (Word 5w)`. -/
def originalOverwrite : Option (LoopStateCell Nat) :=
  some (.word 5)

/-- Transcribed from `set_globals_miss=NONE`. -/
def originalMiss : Option (LoopStateCell Nat) :=
  none

/-- Transcribed from `set_globals_sibling=SOME (Word 1w)`. -/
def originalSibling : Option (LoopStateCell Nat) :=
  some (.word 1)

def emptyGlobals : BitVec 5 → Option (LoopStateCell Nat) :=
  fun _ => none

def oneGlobal : BitVec 5 → Option (LoopStateCell Nat)
  | 3 => some (.word 1)
  | _ => none

def twoGlobals : BitVec 5 → Option (LoopStateCell Nat)
  | 3 => some (.word 1)
  | 4 => some (.word 7)
  | _ => none

#guard updateLoopGlobal emptyGlobals (3 : BitVec 5) (.word 5) (3 : BitVec 5) == originalNew
#guard updateLoopGlobal oneGlobal (3 : BitVec 5) (.word 5) (3 : BitVec 5) == originalOverwrite
#guard updateLoopGlobal emptyGlobals (3 : BitVec 5) (.word 5) (4 : BitVec 5) == originalMiss
#guard updateLoopGlobal twoGlobals (4 : BitVec 5) (.word 7) (3 : BitVec 5) == originalSibling

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop set_globals inserts new global",
        updateLoopGlobal emptyGlobals (3 : BitVec 5) (.word 5) (3 : BitVec 5) == originalNew),
      ("Loop set_globals overwrites existing global",
        updateLoopGlobal oneGlobal (3 : BitVec 5) (.word 5) (3 : BitVec 5) == originalOverwrite),
      ("Loop set_globals leaves missing key absent",
        updateLoopGlobal emptyGlobals (3 : BitVec 5) (.word 5) (4 : BitVec 5) == originalMiss),
      ("Loop set_globals leaves sibling global untouched",
        updateLoopGlobal twoGlobals (4 : BitVec 5) (.word 7) (3 : BitVec 5) == originalSibling) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopSetGlobalsParity
