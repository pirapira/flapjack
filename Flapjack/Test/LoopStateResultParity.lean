import Flapjack.LoopStateResult

/-!
Parity test for the faithful Loop state/result boundary.

The expected values below are transcribed from the checked-in output of the
original Pancake `exit_loop` HOL probe:
`scripts/hol-probes/loop_sem_exit_loop_probe.out`, produced by
`scripts/hol-probes/loop_sem_exit_loop_probeScript.sml` and regenerated with

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml CAKEML=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

Original source: `cakeml/pancake/semantics/loopSemScript.sml:272-276`
(`exit_loop_def`) and `:42` (`dec_clock_def`).
-/

namespace Flapjack.Test.LoopStateResultParity

open Flapjack

def breakDecrements : Bool :=
  exitLoop (α := Nat) (some (.break 3)) == some (.break 2)

def breakStopsAtZero : Bool :=
  exitLoop (α := Nat) (some (.break 0)) == some (.break 0)

def continueDecrements : Bool :=
  exitLoop (α := Nat) (some (.continue 2)) == some (.continue 1)

def otherUnchanged : Bool :=
  exitLoop (α := Nat) (some (.timeOut : LoopMachineResult Nat)) == some .timeOut

def noneStaysNone : Bool :=
  (exitLoop (α := Nat) (none : Option (LoopMachineResult Nat))).isNone

def errorUnchanged : Bool :=
  exitLoop (α := Nat) (some (.error : LoopMachineResult Nat)) == some .error

def probeState (clock : Nat) : LoopMachineState Nat :=
  { locals := fun _ => none
  , globals := fun _ => none
  , memory := fun _ => none
  , mdomain := fun _ => false
  , shMdomain := fun _ => false
  , clock := clock
  , code := []
  , be := false
  , ffi := 0
  , baseAddr := 0
  , topAddr := 0 }

def clockDecrements : Bool :=
  (decrementLoopClock (probeState 5)).clock == 4

def clockStopsAtZero : Bool :=
  (decrementLoopClock (probeState 0)).clock == 0

#guard breakDecrements
#guard breakStopsAtZero
#guard continueDecrements
#guard otherUnchanged
#guard noneStaysNone
#guard errorUnchanged
#guard clockDecrements
#guard clockStopsAtZero

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Loop exit_loop decrements a break counter", breakDecrements),
    ("Loop exit_loop stops a break counter at zero", breakStopsAtZero),
    ("Loop exit_loop decrements a continue counter", continueDecrements),
    ("Loop exit_loop leaves other results unchanged", otherUnchanged),
    ("Loop exit_loop leaves an absent result absent", noneStaysNone),
    ("Loop exit_loop leaves an error result unchanged", errorUnchanged),
    ("Loop dec_clock decrements the clock", clockDecrements),
    ("Loop dec_clock stops the clock at zero", clockStopsAtZero)]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopStateResultParity
