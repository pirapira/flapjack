import Flapjack.CrepExitLoop

/-!
# Parity checks for Crepe `exit_loop_def`

The direct HOL fixture in `scripts/hol-probes/crep_exit_loop_probe.out` is
generated from `crepSemScript.sml:234-237`.  The Lean checks cover both label
decrement cases, the zero boundary, unchanged non-control results, `NONE`,
and preservation of the evaluator state carried by control results.
-/

namespace Flapjack.Test.CrepExitLoopParity

open Flapjack

def sourceState : CrepState Nat where
  locals := fun name => if name == 1 then some 7 else none
  memory := fun address => if address == 8 then some 9 else none
  globals := fun address => if address == 3 then some 5 else none

def breakDecrements : Bool :=
  match crepExitLoop (some (.broke sourceState 3)) with
  | some (.broke state 2) =>
      state.locals 1 == some 7 && state.memory 8 == some 9 &&
        state.globals 3 == some 5
  | _ => false

def breakStopsAtZero : Bool :=
  match crepExitLoop (some (.broke sourceState 0)) with
  | some (.broke state 0) => state.locals 1 == some 7
  | _ => false

def continueDecrements : Bool :=
  match crepExitLoop (some (.continued sourceState 2)) with
  | some (.continued state 1) => state.memory 8 == some 9
  | _ => false

def otherUnchanged : Bool :=
  match crepExitLoop (some (.normal sourceState)) with
  | some (.normal state) => state.globals 3 == some 5
  | _ => false

def noneStaysNone : Bool :=
  (crepExitLoop (α := Nat) none).isNone

#guard breakDecrements
#guard breakStopsAtZero
#guard continueDecrements
#guard otherUnchanged
#guard noneStaysNone

def runChecks : IO Bool := do
  if breakDecrements then
    IO.println "PASS crep exit_loop decrements Break and preserves state"
  else
    IO.println "FAIL crep exit_loop decrements Break and preserves state"
  if breakStopsAtZero then
    IO.println "PASS crep exit_loop keeps zero Break at zero"
  else
    IO.println "FAIL crep exit_loop keeps zero Break at zero"
  if continueDecrements then
    IO.println "PASS crep exit_loop decrements Continue"
  else
    IO.println "FAIL crep exit_loop decrements Continue"
  if otherUnchanged then
    IO.println "PASS crep exit_loop preserves normal result"
  else
    IO.println "FAIL crep exit_loop preserves normal result"
  if noneStaysNone then
    IO.println "PASS crep exit_loop preserves NONE"
  else
    IO.println "FAIL crep exit_loop preserves NONE"
  pure (breakDecrements && breakStopsAtZero && continueDecrements &&
    otherUnchanged && noneStaysNone)

end Flapjack.Test.CrepExitLoopParity
