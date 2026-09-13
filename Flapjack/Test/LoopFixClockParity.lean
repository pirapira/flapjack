import Flapjack.LoopFfi
import Flapjack.Test.LoopFfi

/-!
# Original-domain parity for `fix_clock`

The original definition is
`cakeml/pancake/semantics/loopSemScript.sml:46-49`:
`fix_clock old_s (res,new_s)` preserves `res` and clamps `new_s.clock` to the
smaller of the old and new clocks.  The expected clock observations are direct
HOL-EVAL results from `scripts/hol-probes/loop_sem_fix_clock_probeScript.sml`,
checked in at `scripts/hol-probes/loop_sem_fix_clock_probe.out`.
-/

namespace Flapjack.Test.LoopFixClockParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/loopSemScript.sml:46-49 (fix_clock_def)"

def originalLowerNew : Nat := 4
def originalLowerOld : Nat := 4
def originalZero : Nat := 0

def oldState : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with clock := 10 }

def newStateLower : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with clock := 4 }

def newStateHigher : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with clock := 10 }

def newStateZero : LoopFfiState Nat Unit :=
  { loopByteFfiTestState with clock := 0 }

#guard originalProbeSource ==
  "cakeml/pancake/semantics/loopSemScript.sml:46-49 (fix_clock_def)"
#guard (fixLoopClock oldState (7, newStateLower)).1 == 7
#guard (fixLoopClock oldState (7, newStateLower)).2.clock == originalLowerNew
#guard (fixLoopClock { oldState with clock := 4 } (7, newStateHigher)).2.clock ==
  originalLowerOld
#guard (fixLoopClock { oldState with clock := 0 } (7, newStateZero)).2.clock ==
  originalZero

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop fix_clock preserves the result",
        (fixLoopClock oldState (7, newStateLower)).1 == 7),
      ("Loop fix_clock keeps a lower new clock",
        (fixLoopClock oldState (7, newStateLower)).2.clock == originalLowerNew),
      ("Loop fix_clock clamps a higher new clock",
        (fixLoopClock { oldState with clock := 4 } (7, newStateHigher)).2.clock ==
          originalLowerOld),
      ("Loop fix_clock handles zero clocks",
        (fixLoopClock { oldState with clock := 0 } (7, newStateZero)).2.clock ==
          originalZero) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopFixClockParity
