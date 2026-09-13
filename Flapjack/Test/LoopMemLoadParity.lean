import Flapjack.LoopMemLoad

/-!
# Original-domain parity for `loopSem.mem_load`

Expected observations are transcribed from direct HOL-EVAL of
`cakeml/pancake/semantics/loopSemScript.sml:64-69`, checked in at
`scripts/hol-probes/loop_sem_mem_load_probe.out`.
-/

namespace Flapjack.Test.LoopMemLoadParity

open Flapjack

def memory : Nat → Option Nat :=
  fun address => if address = 3 then some 7 else none

def domain : Nat → Bool :=
  fun address => address == 3

def hit : Bool := loopMemLoad domain memory 3 = some 7
def miss : Bool := loopMemLoad domain memory 4 = none

#guard hit
#guard miss

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop mem_load reads an in-domain address", hit),
      ("Loop mem_load rejects an out-of-domain address", miss) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopMemLoadParity
