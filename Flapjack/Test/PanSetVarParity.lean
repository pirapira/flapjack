import Flapjack.PanValues

/-!
Parity test for the faithful source `set_var`.

The expected values below are transcribed from the checked-in output of the
original Pancake `set_var` HOL probe:
`scripts/hol-probes/pan_sem_set_var_probe.out`, produced by
`scripts/hol-probes/pan_sem_set_var_probeScript.sml` and regenerated with

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml CAKEML=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

Original source: `cakeml/pancake/semantics/panSemScript.sml:398-401`
(`set_var_def`): `set_var v value s = s with locals := s.locals |+ (v,value)`.
The probe fixes `'a = 8`.
-/

namespace Flapjack.Test.PanSetVarParity

open Flapjack

/-- 8-bit word literal. -/
def w8 (value : Nat) : BitVec 8 := BitVec.ofNat 8 value

/-- Source variable state with the original `locals`/`globals` split. -/
structure PanVarState where
  locals : VarName → Option (PanValue (BitVec 8))
  globals : VarName → Option (PanValue (BitVec 8))

/-- Faithful port of `set_var`: update `locals` only. -/
def setVar (state : PanVarState) (name : VarName) (value : PanValue (BitVec 8)) : PanVarState :=
  { state with locals := updatePanValueMap state.locals name value }

/-- Reads a word value as a `Nat`, mirroring the probe's `w2n` output. -/
def read (values : VarName → Option (PanValue (BitVec 8))) (name : VarName) : Option Nat :=
  (values name).bind (fun value =>
    match value with
    | .word word => some word.toNat
    | _ => none)

/-- Base state from the probe: `locals = {x:5, y:7}`, `globals = {g:1}`. -/
def baseState : PanVarState :=
  { locals := updatePanValueMap
      (updatePanValueMap (fun _ => none) "x" (.word (w8 5))) "y" (.word (w8 7))
    globals := updatePanValueMap (fun _ => none) "g" (.word (w8 1)) }

def newLocal : Bool := read (setVar baseState "z" (.word (w8 9))).locals "z" == some 9

def overwrite : Bool := read (setVar baseState "x" (.word (w8 9))).locals "x" == some 9

def otherLocal : Bool := read (setVar baseState "x" (.word (w8 9))).locals "y" == some 7

def globalsUntouched : Bool :=
  read (setVar baseState "x" (.word (w8 9))).globals "g" == some 1

def missingStaysAbsent : Bool := read (setVar baseState "x" (.word (w8 9))).locals "w" == none

#guard newLocal
#guard overwrite
#guard otherLocal
#guard globalsUntouched
#guard missingStaysAbsent

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Pan set_var inserts a new local", newLocal),
    ("Pan set_var overwrites an existing local", overwrite),
    ("Pan set_var leaves sibling locals untouched", otherLocal),
    ("Pan set_var leaves globals untouched", globalsUntouched),
    ("Pan set_var leaves missing locals absent", missingStaysAbsent)]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.PanSetVarParity