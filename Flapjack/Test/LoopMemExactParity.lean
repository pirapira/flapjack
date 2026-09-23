import Flapjack.Pancake.Semantics.LoopSem

/-!
# Exact width-generic parity for `loopSem.mem_load` / `mem_store`

`memLoadHOL`/`memStoreHOL` are the exact HOL-shaped ports of
`cakeml/pancake/semantics/loopSemScript.sml:64-69` and `:57-62` (total
`word_loc` memory, address-set domain).  The expected observations match the
direct HOL-EVAL probes at `scripts/hol-probes/loop_sem_mem_load_probe.out`
(`mem_load_hit=SOME (Word 7w)`, `mem_load_miss=NONE`) and
`scripts/hol-probes/loop_sem_mem_store_probe.out` (`mem_store_hit=SOME (Word 7w)`,
`mem_store_miss=NONE`).
-/

namespace Flapjack.Test.LoopMemExactParity

open Flapjack

abbrev Word := RiscV.Word 64

def totalMemory : Word → LoopValue Word :=
  fun address => if address = 3 then .word 7 else .loc 0 0

abbrev totalDomain : Word → Prop :=
  fun address => address = 3

def loadHit : Bool := memLoadHOL totalMemory totalDomain (3 : Word) = some (.word 7)
def loadMiss : Bool := memLoadHOL totalMemory totalDomain (4 : Word) = none

def storeHit : Bool :=
  (memStoreHOL totalMemory totalDomain (3 : Word) (.word 9)).map (fun memory => memory 3)
    = some (.word 9)
def storeMiss : Bool := memStoreHOL totalMemory totalDomain (4 : Word) (.word 9) = none
def storeKeepsOther : Bool :=
  (memStoreHOL totalMemory totalDomain (3 : Word) (.word 9)).map (fun memory => memory 4)
    = some (.loc 0 0)

#guard loadHit
#guard loadMiss
#guard storeHit
#guard storeMiss
#guard storeKeepsOther

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop mem_load exact hit reads in-domain word", loadHit),
      ("Loop mem_load exact miss rejects out-of-domain address", loadMiss),
      ("Loop mem_store exact hit updates the addressed cell", storeHit),
      ("Loop mem_store exact miss rejects out-of-domain address", storeMiss),
      ("Loop mem_store exact leaves other cells unchanged", storeKeepsOther) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopMemExactParity
