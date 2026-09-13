import Flapjack.LoopMemStore

/-!
# Original-domain parity for `loopSem.mem_store`

Expected observations are transcribed from direct HOL-EVAL of
`cakeml/pancake/semantics/loopSemScript.sml:57-62`, checked in at
`scripts/hol-probes/loop_sem_mem_store_probe.out`.
-/

namespace Flapjack.Test.LoopMemStoreParity

open Flapjack

def memory : Nat → Option Nat :=
  fun address => if address = 3 then some 1 else none

def domain : Nat → Bool :=
  fun address => address == 3

def hit : Bool :=
  (loopMemStore domain memory 3 7).map (fun updated => updated 3) = some (some 7)

def miss : Bool := loopMemStore domain memory 4 7 = none

def otherMemory : Nat → Option Nat :=
  fun address => if address = 4 then some 1 else none

def otherDomain : Nat → Bool :=
  fun address => address == 3 || address == 4

def other : Bool :=
  (loopMemStore otherDomain otherMemory 3 7).map (fun updated => updated 4) = some (some 1)

#guard hit
#guard miss
#guard other

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop mem_store updates an in-domain address", hit),
      ("Loop mem_store rejects an out-of-domain address", miss),
      ("Loop mem_store preserves another address", other) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopMemStoreParity
