import Flapjack.LoopFfi
import Flapjack.Test.LoopFfi

/-!
# Original-domain parity for `dec_clock`

The original definition is
`cakeml/pancake/semantics/loopSemScript.sml:42-43`:
`dec_clock s = s with clock := s.clock - 1`.
The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_sem_dec_clock_probeScript.sml`, checked in at
`scripts/hol-probes/loop_sem_dec_clock_probe.out`.
-/

namespace Flapjack.Test.LoopDecClockParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/loopSemScript.sml:42-43 (dec_clock_def)"

def originalFive : Nat := 4
def originalZero : Nat := 0
def originalLocal : Option (List Nat) := some [7]

def localProbeState : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with
    locals := fun name => if name == 1 then some 7 else none }

def read (state : LoopFfiState Nat Unit) (names : List Nat) : Option (List Nat) :=
  loopReadLocals state.locals names

#guard originalProbeSource ==
  "cakeml/pancake/semantics/loopSemScript.sml:42-43 (dec_clock_def)"
#guard (decLoopClock { loopByteFfiTestState with clock := 5 }).clock == originalFive
#guard (decLoopClock { loopByteFfiTestState with clock := 0 }).clock == originalZero
#guard read (decLoopClock { localProbeState with clock := 9 }) [1] == originalLocal

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop dec_clock decrements a positive clock",
        (decLoopClock { loopByteFfiTestState with clock := 5 }).clock == originalFive),
      ("Loop dec_clock saturates at zero",
        (decLoopClock { loopByteFfiTestState with clock := 0 }).clock == originalZero),
      ("Loop dec_clock preserves locals",
        read (decLoopClock { localProbeState with clock := 9 }) [1] == originalLocal) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopDecClockParity
