import Flapjack.CrepFixClock
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$fix_clock_def`

The direct HOL fixture in `scripts/hol-probes/crep_fix_clock_probe.out`
checks both branches of the source minimum.  The executable checks also pin
the result and representative locals, which are preserved by the record
update.
-/

namespace Flapjack.Test.CrepFixClockParity

open Flapjack

def clampStep : CrepRuntimeStep Nat Unit String :=
  (.returned [7], { crepeRuntimeState with
    locals := fun name => if name == 1 then some 7 else none,
    clock := 9 })

def lowerStep : CrepRuntimeStep Nat Unit String :=
  (.returned [7], { crepeRuntimeState with
    locals := fun name => if name == 1 then some 7 else none,
    clock := 3 })

def observeClamp : Bool :=
  match crepFixClock { crepeRuntimeState with clock := 5 }
      clampStep with
  | (.returned [7], state) =>
      state.clock == 5 && state.locals 1 == some 7
  | _ => false

def observeLower : Bool :=
  match crepFixClock { crepeRuntimeState with clock := 5 }
      lowerStep with
  | (.returned [7], state) =>
      state.clock == 3 && state.locals 1 == some 7
  | _ => false

#guard observeClamp
#guard observeLower

def runChecks : IO Bool := do
  if observeClamp then IO.println "PASS crep fix_clock clamps higher new clock"
  else IO.println "FAIL crep fix_clock clamps higher new clock"
  if observeLower then IO.println "PASS crep fix_clock keeps lower new clock"
  else IO.println "FAIL crep fix_clock keeps lower new clock"
  pure (observeClamp && observeLower)

end Flapjack.Test.CrepFixClockParity
