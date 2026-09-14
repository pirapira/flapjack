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

#guard originalSource ==
  "cakeml/pancake/semantics/panSemScript.sml:441-443 (dec_clock_def)"
#guard observeFive
#guard observeZero

def runChecks : IO Bool := do
  if observeFive then IO.println "PASS Pan dec_clock decrements" else
    IO.println "FAIL Pan dec_clock decrements"
  if observeZero then IO.println "PASS Pan dec_clock saturates" else
    IO.println "FAIL Pan dec_clock saturates"
  pure (observeFive && observeZero)

end Flapjack.Test.PanDecClockParity
