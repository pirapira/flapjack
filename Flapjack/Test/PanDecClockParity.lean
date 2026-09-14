import Flapjack.PanValueFfiClockSemantics

/-!
# Original-domain parity for `panSem.dec_clock_def`

The direct HOL fixture in `scripts/hol-probes/pan_dec_clock_probe.out` is
generated from `cakeml/pancake/semantics/panSemScript.sml:441-443`.  The Lean
clocked evaluator carries state components separately, so `decPanClock` is
the corresponding exact clock-field update and is exercised at positive and
zero clocks.
-/

namespace Flapjack.Test.PanDecClockParity

open Flapjack

def originalSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:441-443 (dec_clock_def)"

def observeFive : Bool := decPanClock 5 == 4
def observeZero : Bool := decPanClock 0 == 0

def observeFixClamp : Bool :=
  (fixPanClock 5 ((), 7) : Unit × Nat).2 == 5

def observeFixLower : Bool :=
  (fixPanClock 5 ((), 3) : Unit × Nat).2 == 3

#guard originalSource ==
  "cakeml/pancake/semantics/panSemScript.sml:441-443 (dec_clock_def)"
#guard observeFive
#guard observeZero
#guard observeFixClamp
#guard observeFixLower

def runChecks : IO Bool := do
  if observeFive then IO.println "PASS Pan dec_clock decrements" else
    IO.println "FAIL Pan dec_clock decrements"
  if observeZero then IO.println "PASS Pan dec_clock saturates" else
    IO.println "FAIL Pan dec_clock saturates"
  if observeFixClamp then IO.println "PASS Pan fix_clock clamps" else
    IO.println "FAIL Pan fix_clock clamps"
  if observeFixLower then IO.println "PASS Pan fix_clock keeps lower" else
    IO.println "FAIL Pan fix_clock keeps lower"
  pure (observeFive && observeZero && observeFixClamp && observeFixLower)

end Flapjack.Test.PanDecClockParity
