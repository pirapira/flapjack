import Flapjack.LoopMemoryState

/-!
# Exact Loop memory-state adapter checks

The concrete observations correspond to the original HOL probes
`loop_sem_mem_load_probe.out` and `loop_sem_mem_store_probe.out`.  These
checks exercise the adapter that will replace the legacy domain-free memory
boundary during exact Loop evaluator migration.
-/

namespace Flapjack.Test.LoopMemoryStateParity

open Flapjack

def state : LoopMemoryState Nat :=
  { memory := fun address => if address = 3 then some 1 else none
    domain := fun address => address == 3 }

def loadHit : Bool := loopMemoryLoad state 3 = some 1
def loadMiss : Bool := loopMemoryLoad state 4 = none
def storeHit : Bool :=
  (loopMemoryStore state 3 7).map (fun updated => updated.memory 3) = some (some 7)
def storeMiss : Bool := loopMemoryStore state 4 7 = none

#guard loadHit
#guard loadMiss
#guard storeHit
#guard storeMiss

def runChecks : IO Bool := do
  let checks :=
    [ ("Exact Loop memory adapter loads in-domain", loadHit),
      ("Exact Loop memory adapter rejects out-of-domain load", loadMiss),
      ("Exact Loop memory adapter stores in-domain", storeHit),
      ("Exact Loop memory adapter rejects out-of-domain store", storeMiss) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopMemoryStateParity
