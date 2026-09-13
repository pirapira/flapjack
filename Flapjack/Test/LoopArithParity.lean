import Flapjack.LoopArith

/-!
Parity test for the faithful `loop_arith` port.

The expected values below are transcribed from the checked-in output of the
original Pancake `loop_arith` HOL probe:
`scripts/hol-probes/loop_sem_loop_arith_probe.out`, produced by
`scripts/hol-probes/loop_sem_loop_arith_probeScript.sml` and regenerated with

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml CAKEML=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

Original source: `cakeml/pancake/semantics/loopSemScript.sml:118-145`
(`loop_arith_def`). The probe fixes `'a = 8`, so `dimword (:'a) = 256`.
-/

namespace Flapjack.Test.LoopArithParity

open Flapjack

/-- Word width used by the probe, giving `dimword = 256`. -/
def probeWidth : Nat := 8

/-- Local environment built from `(register, value)` pairs. -/
def withLocals (pairs : List (Nat × Nat)) : Nat → Option Nat :=
  fun register => (pairs.find? (fun entry => entry.1 == register)).map (·.2)

/-- Reads the requested registers back out of an arithmetic result. -/
def read (locals : Nat → Option Nat) (registers : List Nat) : Option (List Nat) :=
  loopReadLocals locals registers

def divResult : Option (List Nat) :=
  (loopArith probeWidth (.div 1 2 3) (withLocals [(2, 7), (3, 2)])).bind
    (fun locals => read locals [1])

def divByZero : Bool :=
  (loopArith probeWidth (.div 1 2 3) (withLocals [(2, 7), (3, 0)])).isNone

/-- The original returns `NONE` for a non-word operand; the `Nat` model has no
    non-word locals, so an absent operand is the corresponding input. -/
def divNonWord : Bool :=
  (loopArith probeWidth (.div 1 2 3) (withLocals [(3, 2)])).isNone

def longMulResult : Option (List Nat) :=
  (loopArith probeWidth (.longMul 1 2 3 4) (withLocals [(3, 20), (4, 20)])).bind
    (fun locals => read locals [1, 2])

def longMulNonWord : Bool :=
  (loopArith probeWidth (.longMul 1 2 3 4) (withLocals [(4, 20)])).isNone

/-- The original inner update writes the low word and the outer update writes
    the high word, so the high word wins when the destinations coincide. -/
def longMulSameDestination : Option (List Nat) :=
  (loopArith probeWidth (.longMul 1 1 3 4) (withLocals [(3, 20), (4, 20)])).bind
    (fun locals => read locals [1])

def longDivResult : Option (List Nat) :=
  (loopArith probeWidth (.longDiv 1 2 3 4 5) (withLocals [(3, 1), (4, 3), (5, 2)])).bind
    (fun locals => read locals [1, 2])

def longDivByZero : Bool :=
  (loopArith probeWidth (.longDiv 1 2 3 4 5) (withLocals [(3, 1), (4, 3), (5, 0)])).isNone

def longDivOverflow : Bool :=
  (loopArith probeWidth (.longDiv 1 2 3 4 5) (withLocals [(3, 1), (4, 0), (5, 1)])).isNone

/-- The original inner update writes the remainder and the outer update writes
    the quotient, so the quotient wins when the destinations coincide. -/
def longDivSameDestination : Option (List Nat) :=
  (loopArith probeWidth (.longDiv 1 1 3 4 5) (withLocals [(3, 1), (4, 3), (5, 2)])).bind
    (fun locals => read locals [1])

#guard divResult == some [3]
#guard divByZero
#guard divNonWord
#guard longMulResult == some [1, 144]
#guard longMulNonWord
#guard longMulSameDestination == some [144]
#guard longDivResult == some [129, 1]
#guard longDivByZero
#guard longDivOverflow
#guard longDivSameDestination == some [129]

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Loop loop_arith divides words", divResult == some [3]),
    ("Loop loop_arith rejects division by zero", divByZero),
    ("Loop loop_arith rejects a missing operand", divNonWord),
    ("Loop loop_arith splits a long multiplication", longMulResult == some [1, 144]),
    ("Loop loop_arith rejects a missing long-mul operand", longMulNonWord),
    ("Loop loop_arith keeps the high word on a shared destination",
      longMulSameDestination == some [144]),
    ("Loop loop_arith divides a wide numerator", longDivResult == some [129, 1]),
    ("Loop loop_arith rejects a zero long divisor", longDivByZero),
    ("Loop loop_arith rejects an overflowing long quotient", longDivOverflow),
    ("Loop loop_arith keeps the quotient on a shared destination",
      longDivSameDestination == some [129])]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopArithParity
