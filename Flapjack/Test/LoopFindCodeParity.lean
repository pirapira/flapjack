import Flapjack.LoopFindCode

/-!
Parity test for the faithful `find_code` port.

The expected values below are transcribed from the checked-in output of the
original Pancake `find_code` HOL probe:
`scripts/hol-probes/loop_sem_find_code_probe.out`, produced by
`scripts/hol-probes/loop_sem_find_code_probeScript.sml` and regenerated with

```
HOL4=/home/zksecurity/HOL CAKEMLDIR=$PWD/cakeml CAKEML=$PWD/cakeml \
  bash scripts/hol-probes/regenerate.sh
```

Original source: `cakeml/pancake/semantics/loopSemScript.sml:147-163`.
-/

namespace Flapjack.Test.LoopFindCodeParity

open Flapjack

/-- Tag identifying the callee body so tests can distinguish table entries. -/
def loopBodyTag : LoopProg α → Nat
  | .mark _ => 1
  | .tick => 2
  | _ => 0

/-- Table from the probe: label `5` takes two parameters and returns the body
    tagged `1`. -/
def code2 : LoopCode LoopWordLoc := [(5, [1, 2], .mark .skip)]

/-- Table from the probe: label `9` takes one parameter and returns the body
    tagged `2`. -/
def code1 : LoopCode LoopWordLoc := [(9, [7], .tick)]

/-- Table from the probe with duplicate parameter names. -/
def codeDup : LoopCode LoopWordLoc := [(5, [1, 1], .skip)]

def labelFirst : Bool :=
  match findLoopCode (some 5) [.word 3, .word 4] code2 with
  | some (env, body) =>
      (env 1 == some (.word 3)) && (env 2 == some (.word 4)) &&
        (loopBodyTag body == 1)
  | none => false

def labelSecond : Bool :=
  match findLoopCode (some 5) [.word 3, .word 4] code2 with
  | some (env, _) => env 2 == some (.word 4)
  | none => false

def labelLenMismatch : Bool :=
  (findLoopCode (some 5) [.word 3] code2).isNone

def labelMissing : Bool :=
  (findLoopCode (some 6) [.word 3, .word 4] code2).isNone

def linkFirst : Bool :=
  match findLoopCode none [.word 3, .loc 9 0] code1 with
  | some (env, body) => (env 7 == some (.word 3)) && (loopBodyTag body == 2)
  | none => false

def linkWrongLen : Bool :=
  (findLoopCode none [.loc 9 0] code1).isNone

def emptyArgs : Bool :=
  (findLoopCode none [] code1).isNone

def badLast : Bool :=
  (findLoopCode none [.word 3, .word 4] code1).isNone

def duplicateFirstWins : Bool :=
  match findLoopCode (some 5) [.word 5, .word 7] codeDup with
  | some (env, _) => env 1 == some (.word 5)
  | none => false

#guard labelFirst
#guard labelSecond
#guard labelLenMismatch
#guard labelMissing
#guard linkFirst
#guard linkWrongLen
#guard emptyArgs
#guard badLast
#guard duplicateFirstWins

/-- Runs the executable parity checks. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("Loop find_code binds labelled parameters", labelFirst),
    ("Loop find_code binds every labelled parameter", labelSecond),
    ("Loop find_code rejects a labelled length mismatch", labelLenMismatch),
    ("Loop find_code rejects a missing labelled entry", labelMissing),
    ("Loop find_code binds link arguments to parameters", linkFirst),
    ("Loop find_code rejects a link length mismatch", linkWrongLen),
    ("Loop find_code rejects empty link arguments", emptyArgs),
    ("Loop find_code rejects a non-link trailing argument", badLast),
    ("Loop find_code keeps the first duplicate parameter", duplicateFirstWins)]
  let mut ok := true
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  return ok

end Flapjack.Test.LoopFindCodeParity
