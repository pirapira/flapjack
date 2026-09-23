import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.HolRef

/-!
# HOL-shaped whole-state Loop memory/shared-memory regression

Exercises the exact whole-state ports `memLoadSemHOL`, `memStoreSemHOL`,
`shMemStoreSemHOL`/`shMemLoadSemHOL`/`shMemOpSemHOL` from
`Flapjack/Pancake/Semantics/LoopSem.lean` and their explicit bridge to
`LoopMachineState`.  Expected values follow the HOL definitions
`loopSemScript.sml:57-69` and `:198-262`; the aligned-address rule is HOL
`byte_align` (LOG2 of `dimindex DIV 8`).
-/

namespace Flapjack.Test.LoopSemStateParity

open Flapjack

abbrev Word := RiscV.Word 64

def memory : Word → LoopValue Word :=
  fun address =>
    if address = 0 then .word 0xAB
    else if address = 8 then .word 0xEFCD
    else .loc 0 0

abbrev domain : Word → Prop := fun address => address = 0 ∨ address = 8

abbrev sharedDomain : Word → Prop := fun address => address = 4 ∨ address = 8

abbrev baseState : LoopSemState Word Unit where
  locals := fun name =>
    if name = 0 then some (.word 1)
    else if name = 1 then some (.word 3)
    else if name = 2 then some (.word 8)
    else if name = 3 then some (.word 2)
    else none
  globals := fun _ => none
  memory := memory
  mdomain := domain
  shMdomain := sharedDomain
  clock := 200
  code := []
  be := false
  ffi := trivialFfiState Unit ()
  baseAddr := 0
  topAddr := 100

theorem memLoadHit : memLoadSemHOL (0 : Word) baseState = some (.word 0xAB) := by
  decide

theorem memLoadMiss : memLoadSemHOL (4 : Word) baseState = none := by
  decide

theorem memStoreHit :
    (memStoreSemHOL (0 : Word) (.word 9) baseState).map
        (fun state => state.memory 0) = some (.word 9) := by
  decide

/-- A bridge round-trip keeps the total memory value. -/
theorem bridgeMemory :
    (LoopSemState.ofMachine (LoopMachineState.ofSem baseState)).memory 0 =
      .word 0xAB := by
  decide

/-- `load8` at `8` is 8-aligned and lies in the shared domain, so the
    terminal oracle yields `FinalFFI` and clears the locals. -/
def shMemLoadFinalGuard : Bool :=
  match (shMemOpSemHOL (width := 64) .load8 3 (8 : Word) baseState).1 with
  | some (.finalFfi _) => true
  | _ => false

/-- `load8` at `1` aligns down to `0`, which is outside the shared domain, so it
    errors. -/
def shMemLoadOutOfDomainGuard : Bool :=
  match (shMemOpSemHOL (width := 64) .load8 3 (1 : Word) baseState).1 with
  | some .error => true
  | _ => false

/-- `store8` reads the `Word` held in the named local and reaches the oracle. -/
def shMemStoreGuard : Bool :=
  match (shMemOpSemHOL (width := 64) .store8 2 (8 : Word) baseState).1 with
  | some (.finalFfi _) => true
  | _ => false

#guard shMemLoadFinalGuard
#guard shMemLoadOutOfDomainGuard
#guard shMemStoreGuard

def memoryPortsGuard : Bool :=
  decide (memLoadSemHOL (0 : Word) baseState = some (.word 0xAB)) &&
    decide (memLoadSemHOL (4 : Word) baseState = none) &&
    decide ((memStoreSemHOL (0 : Word) (.word 9) baseState).map
      (fun (state : LoopSemState Word Unit) => state.memory 0) = some (.word 9))

#guard memoryPortsGuard

def runChecks : IO Bool := do
  let memoryOk ← if memoryPortsGuard then
      IO.println "PASS Loop whole-state mem_load/mem_store exact ports"
      pure true
    else
      IO.println "FAIL Loop whole-state mem_load/mem_store exact ports"
      pure false
  let shMemOk ← if shMemLoadFinalGuard && shMemLoadOutOfDomainGuard && shMemStoreGuard
      then
        IO.println "PASS Loop whole-state sh_mem_load/store/op exact ports"
        pure true
      else
        IO.println "FAIL Loop whole-state sh_mem_load/store/op exact ports"
        pure false
  pure (memoryOk && shMemOk)

end Flapjack.Test.LoopSemStateParity
