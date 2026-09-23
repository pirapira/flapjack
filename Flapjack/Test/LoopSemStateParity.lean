import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.HolRef

/-!
# HOL-shaped whole-state Loop memory/shared-memory regression

Exercises the exact whole-state ports `memLoadSemHOL`, `memStoreSemHOL`,
`shMemStoreSemHOL`/`shMemLoadSemHOL`/`shMemOpSemHOL`, `setGlobalsSemHOL` and
`getVarImmSemHOL` from
`Flapjack/Pancake/Semantics/LoopSem.lean` and their explicit bridge to
`LoopMachineState`.  Expected values follow the HOL definitions
`loopSemScript.sml:52-69`, `:165-167` and `:198-262`; the aligned-address rule is
HOL `byte_align` (LOG2 of `dimindex DIV 8`).  The width-8 fragments are checked
against the captured outputs of the direct original HOL runs in
`scripts/hol-probes/loop_sem_mem_load_probe.out`,
`loop_sem_mem_store_probe.out` and `loop_sem_sh_mem_load_probe.out`.
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
  code := fun _ => none
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

/-- The one-way bridge maps an absent machine memory cell to HOL's `Loc`. -/
def bridgeMachine : LoopMachineState Word Unit where
  locals := fun _ => none
  globals := fun _ => none
  memory := fun address => if address = 0 then some (.word 0xAB) else none
  mdomain := fun address => address = 0
  shMdomain := fun _ => false
  clock := 200
  code := []
  be := false
  ffi := trivialFfiState Unit ()
  baseAddr := 0
  topAddr := 100

theorem bridgeMemory :
    (LoopSemState.ofMachine bridgeMachine).memory 0 = .word 0xAB := by
  decide

theorem bridgeAbsentIsLoc :
    (LoopSemState.ofMachine bridgeMachine).memory 7 = .loc 0 0 := by
  decide

theorem bridgeCodeEmpty :
    (LoopSemState.ofMachine bridgeMachine).code 7 = none := rfl

theorem setGlobalsHit :
    (setGlobalsSemHOL baseState 0 (.word 42)).globals 0 = some (.word 42) := by
  decide

theorem setGlobalsPreserves :
    (setGlobalsSemHOL baseState 0 (.word 42)).globals 1 = baseState.globals 1 :=
  rfl

theorem getVarImmReg : getVarImmSemHOL baseState (.reg 0) = some (.word 1) :=
  rfl

theorem getVarImmImm :
    getVarImmSemHOL baseState (.imm (5 : Word)) = some (.word 5) :=
  rfl

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

def stateHelpersGuard : Bool :=
  decide ((setGlobalsSemHOL baseState 0 (.word 42)).globals 0 = some (.word 42)) &&
    decide ((setGlobalsSemHOL baseState 0 (.word 42)).globals 1 = none) &&
    decide (getVarImmSemHOL baseState (.reg 1) = some (.word 3)) &&
    decide (getVarImmSemHOL baseState (.imm (5 : Word)) = some (.word 5))

#guard stateHelpersGuard

/-! ## Direct-HOL-probe fixtures

The expected values below are the captured outputs of direct original HOL runs
(`scripts/hol-probes/loop_sem_mem_load_probe.out`,
`loop_sem_mem_store_probe.out`, `loop_sem_sh_mem_load_probe.out`). -/

abbrev Word8 := RiscV.Word 8

def memory8 : Word8 → LoopValue Word8 :=
  fun address => if address = 0 then .word 7 else .loc 0 0

abbrev domain8 : Word8 → Prop := fun address => address = 0

abbrev baseState8 : LoopSemState Word8 Unit where
  locals := fun name => if name = 1 then some (.word 0) else none
  globals := fun _ => none
  memory := memory8
  mdomain := domain8
  shMdomain := fun address => address = 3
  clock := 200
  code := fun _ => none
  be := false
  ffi := trivialFfiState Unit ()
  baseAddr := 0
  topAddr := 100

/-- `mem_load_hit=SOME (Word 7w)`. -/
theorem probeMemLoadHit : memLoadSemHOL (0 : Word8) baseState8 = some (.word 7) := by
  decide

/-- `mem_load_miss=NONE`. -/
theorem probeMemLoadMiss : memLoadSemHOL (1 : Word8) baseState8 = none := by
  decide

/-- `mem_store_hit=SOME (Word 7w)` after reading the stored cell back. -/
theorem probeMemStoreHit :
    (memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
        (fun state => state.memory 0) = some (.word 7) := by
  decide

/-- `mem_store_miss=NONE` (out-of-domain address). -/
theorem probeMemStoreMiss : memStoreSemHOL (1 : Word8) (.word 7) baseState8 = none := by
  decide

/-- Oracle that returns the translated bytes for a `SharedMem MappedRead`. -/
def returningRead : FfiState Unit where
  oracle := fun name _ _ bytes =>
    match name with
    | .sharedMem .mappedRead => .returned () bytes
    | _ => .final .failed
  state := ()
  ioEvents := []

abbrev sharedState8 : LoopSemState Word8 Unit where
  locals := fun name => if name = 1 then some (.word 0) else none
  globals := fun _ => none
  memory := memory8
  mdomain := domain8
  shMdomain := fun address => address = 3
  clock := 200
  code := fun _ => none
  be := false
  ffi := returningRead
  baseAddr := 0
  topAddr := 100

/-- `return_zero_width=(NONE, …, 1)`: the returned bytes set local `1` to `3`
    and one FFI event is appended. -/
def probeShMemReturnGuard : Bool :=
  decide ((shMemLoadSemHOL (width := 8) 1 3 0 sharedState8).1 = none) &&
    decide ((shMemLoadSemHOL (width := 8) 1 3 0 sharedState8).2.locals 1 =
      some (.word 3)) &&
    decide ((shMemLoadSemHOL (width := 8) 1 3 0 sharedState8).2.ffi.ioEvents.length = 1)

/-- `domain_error=(SOME Error, …)`. -/
def probeShMemDomainErrorGuard : Bool :=
  decide ((shMemLoadSemHOL (width := 8) 1 4 0 sharedState8).1 = some .error)

#guard probeShMemReturnGuard
#guard probeShMemDomainErrorGuard

def probeFixturesGuard : Bool :=
  decide ((memLoadSemHOL (0 : Word8) baseState8) = some (.word 7)) &&
    decide ((memLoadSemHOL (1 : Word8) baseState8) = none) &&
    decide ((memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
      (fun (state : LoopSemState Word8 Unit) => state.memory 0) = some (.word 7)) &&
    decide ((memStoreSemHOL (1 : Word8) (.word 7) baseState8) = none) &&
    probeShMemReturnGuard && probeShMemDomainErrorGuard

#guard probeFixturesGuard

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
  let helpersOk ← if stateHelpersGuard then
      IO.println "PASS Loop whole-state set_globals and get_var_imm exact ports"
      pure true
    else
      IO.println "FAIL Loop whole-state set_globals and get_var_imm exact ports"
      pure false
  let probeOk ← if probeFixturesGuard then
      IO.println "PASS Loop whole-state direct HOL probe fixtures (mem/sh_mem)"
      pure true
    else
      IO.println "FAIL Loop whole-state direct HOL probe fixtures (mem/sh_mem)"
      pure false
  pure (memoryOk && shMemOk && helpersOk && probeOk)

end Flapjack.Test.LoopSemStateParity
