import Flapjack.LoopSetVars

/-!
# Original-domain parity for `set_vars` / `loopSetVars`

`Flapjack.loopSetVars` (Flapjack/LoopSetVars.lean) is the Lean counterpart of
the original Pancake `set_vars` definition:

```
cakeml/pancake/semantics/loopSemScript.sml:113-116 (set_vars_def)
  set_vars vs xs s = s with locals := alist_insert vs xs s.locals
```

The original `alist_insert` (sptreeScript.sml:2085-2089) inserts from the tail
towards the head, so the FIRST occurrence of a repeated name wins and a longer
name list truncates against the value list.  The expected values below are
transcribed from the checked-in HOL EVAL probe output
`scripts/hol-probes/loop_sem_set_vars_probe.out`, produced by
`scripts/hol-probes/loop_sem_set_vars_probeScript.sml` (which reads the state
back through the original `get_vars`, since sptree lookup is `[nocompute]`).
Regenerate with:

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

The homogeneous Lean counterpart models locals as `Nat → Option Nat`; the
probe's word values `Word nw` are transcribed as the numeral `n`.  Reads use
`Flapjack.loopReadLocals`, the Lean counterpart of the original `get_vars`
(loopSemScript.sml:98-106), so only the observed lookup result is compared.
The probe's `set_vars_clock` observation is not modelled because the Lean
`LoopState` has no clock field.
-/

namespace Flapjack.Test.LoopSetVarsParity

open Flapjack

/-- Transcribed from `set_vars_basic=SOME [Word 5w; Word 7w]`. -/
def originalBasic : Option (List Nat) :=
  some [5, 7]

/-- Transcribed from `set_vars_missing=NONE`. -/
def originalMissing : Option (List Nat) :=
  none

/-- Transcribed from `set_vars_duplicate=SOME [Word 5w]` (first occurrence wins). -/
def originalDuplicate : Option (List Nat) :=
  some [5]

/-- Transcribed from `set_vars_overwrite=SOME [Word 9w]`. -/
def originalOverwrite : Option (List Nat) :=
  some [9]

/-- Transcribed from `set_vars_empty=NONE`. -/
def originalEmpty : Option (List Nat) :=
  none

def emptyLocals : Nat → Option Nat :=
  fun _ => none

def oneLocal : Nat → Option Nat
  | 1 => some 1
  | _ => none

def read (locals : Nat → Option Nat) (names : List Nat) : Option (List Nat) :=
  loopReadLocals locals names

#guard read (loopSetVars emptyLocals [1, 2] [5, 7]) [1, 2] == originalBasic
#guard read (loopSetVars emptyLocals [1, 2] [5, 7]) [3] == originalMissing
#guard read (loopSetVars emptyLocals [1, 1] [5, 7]) [1] == originalDuplicate
#guard read (loopSetVars emptyLocals [1, 2] [5]) [1, 2] == originalMissing
#guard read (loopSetVars emptyLocals [1, 2] [5]) [1] == some [5]
#guard read (loopSetVars oneLocal [1] [9]) [1] == originalOverwrite
#guard read (loopSetVars emptyLocals [] []) [1] == originalEmpty

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop set_vars assigns a parallel list",
        read (loopSetVars emptyLocals [1, 2] [5, 7]) [1, 2] == originalBasic),
      ("Loop set_vars leaves unassigned names absent",
        read (loopSetVars emptyLocals [1, 2] [5, 7]) [3] == originalMissing),
      ("Loop set_vars first occurrence wins on duplicates",
        read (loopSetVars emptyLocals [1, 1] [5, 7]) [1] == originalDuplicate),
      ("Loop set_vars truncates to the shorter list",
        read (loopSetVars emptyLocals [1, 2] [5]) [1, 2] == originalMissing),
      ("Loop set_vars overwrites an existing local",
        read (loopSetVars oneLocal [1] [9]) [1] == originalOverwrite),
      ("Loop set_vars on empty lists changes nothing",
        read (loopSetVars emptyLocals [] []) [1] == originalEmpty) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopSetVarsParity
