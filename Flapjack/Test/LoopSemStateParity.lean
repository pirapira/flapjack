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
against the direct original HOL run
`scripts/hol-probes/loop_sem_whole_state_probeScript.sml`
(output `loop_sem_whole_state_probe.out`): raw `mem_load` hit/miss, the
`mem_store` update observing an untouched neighbouring cell, and the
`sh_mem_load`/`sh_mem_store` return/final/out-of-domain rows.
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

The expected values below are the direct original HOL run
`scripts/hol-probes/loop_sem_whole_state_probeScript.sml`
(output `loop_sem_whole_state_probe.out`); each row exposes a concrete value
(raw `SOME`/`NONE`, concrete words, io-event count) rather than a collapsed
default. -/

abbrev Word8 := RiscV.Word 8

def memory8 : Word8 → LoopValue Word8 :=
  fun address => if address = 0 then .word 7 else if address = 1 then .word 2 else .loc 0 0

abbrev domain8 : Word8 → Prop := fun address => address = 0 ∨ address = 1

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

/-- `mem_load_miss=NONE` (out-of-domain address). -/
theorem probeMemLoadMiss : memLoadSemHOL (5 : Word8) baseState8 = none := by
  decide

/-- `mem_store_update`: storing `Word 7w` at `0` keeps the `1` entry `Word 2w`. -/
theorem probeMemStoreKeepsOther :
    (memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
        (fun state => state.memory 1) = some (.word 2) := by
  decide

/-- `mem_store_hit=SOME (Word 7w)` after reading the stored cell back. -/
theorem probeMemStoreHit :
    (memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
        (fun state => state.memory 0) = some (.word 7) := by
  decide

/-- `mem_store_miss=NONE` (out-of-domain address). -/
theorem probeMemStoreMiss : memStoreSemHOL (5 : Word8) (.word 7) baseState8 = none := by
  decide

/-- Oracle that returns the translated bytes for any shared-memory access
    (`MappedRead` and `MappedWrite`), matching the direct HOL probe. -/
def returningRead : FfiState Unit where
  oracle := fun name _ _ bytes =>
    match name with
    | .sharedMem _ => .returned () bytes
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

/-- Oracle that always finalizes, matching the direct HOL probe. -/
def finalRead : FfiState Unit where
  oracle := fun _ _ _ _ => .final .failed
  state := ()
  ioEvents := []

/-- State with local `1` holding `Word 7w` for the store probes. -/
abbrev storingState8 : LoopSemState Word8 Unit where
  locals := fun name => if name = 1 then some (.word 7) else none
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

/-- `store_return=(NONE, 7w)`: only the ffi is updated, the stored local stays. -/
def probeShMemStoreReturnGuard : Bool :=
  decide ((shMemStoreSemHOL (width := 8) 1 3 0 storingState8).1 = none) &&
    decide ((shMemStoreSemHOL (width := 8) 1 3 0 storingState8).2.locals 1 = some (.word 7))

/-- `load_final`: a final event is produced and locals are cleared. -/
def probeShMemLoadFinalGuard : Bool :=
  decide (shMemLoadSemHOL (width := 8) 1 3 0
      { sharedState8 with ffi := finalRead }).1.isSome &&
    decide ((shMemLoadSemHOL (width := 8) 1 3 0
      { sharedState8 with ffi := finalRead }).2.locals 1 = none)

/-- `store_final`: a final event is produced and locals are cleared. -/
def probeShMemStoreFinalGuard : Bool :=
  decide (shMemStoreSemHOL (width := 8) 1 3 0
      { storingState8 with ffi := finalRead }).1.isSome &&
    decide ((shMemStoreSemHOL (width := 8) 1 3 0
      { storingState8 with ffi := finalRead }).2.locals 1 = none)

#guard probeShMemReturnGuard
#guard probeShMemDomainErrorGuard
#guard probeShMemStoreReturnGuard
#guard probeShMemLoadFinalGuard
#guard probeShMemStoreFinalGuard

def probeFixturesGuard : Bool :=
  decide ((memLoadSemHOL (0 : Word8) baseState8) = some (.word 7)) &&
    decide ((memLoadSemHOL (5 : Word8) baseState8) = none) &&
    decide ((memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
      (fun (state : LoopSemState Word8 Unit) => state.memory 0) = some (.word 7)) &&
    decide ((memStoreSemHOL (0 : Word8) (.word 7) baseState8).map
      (fun (state : LoopSemState Word8 Unit) => state.memory 1) = some (.word 2)) &&
    decide ((memStoreSemHOL (5 : Word8) (.word 7) baseState8) = none) &&
    probeShMemReturnGuard && probeShMemDomainErrorGuard &&
    probeShMemStoreReturnGuard && probeShMemLoadFinalGuard && probeShMemStoreFinalGuard

#guard probeFixturesGuard

/-! ## Whole-state `loop_arith` fixtures

Small width-8 state where every arithmetic result is checkable exactly:
`dimword = 2 ^ 8 = 256`. Locals: `0 -> 1`, `1 -> 3`, `2 -> 8`, `3 -> 2`,
`5 -> 255`, `6 -> 255`, `7 -> 1`, `8 -> 0`. -/

abbrev arithState8 : LoopSemState Word8 Unit where
  locals := fun name =>
    if name = 0 then some (.word 1)
    else if name = 1 then some (.word 3)
    else if name = 2 then some (.word 8)
    else if name = 3 then some (.word 2)
    else if name = 5 then some (.word 255)
    else if name = 6 then some (.word 255)
    else if name = 7 then some (.word 1)
    else if name = 8 then some (.word 0)
    else none
  globals := fun _ => none
  memory := fun _ => .loc 0 0
  mdomain := fun _ => False
  shMdomain := fun _ => False
  clock := 200
  code := fun _ => none
  be := false
  ffi := trivialFfiState Unit ()
  baseAddr := 0
  topAddr := 100

def loopArithGuard : Bool :=
  -- LDiv: 8 / 3 = 2
  decide ((loopArithSemHOL arithState8 (.div 4 2 1)).map
      (fun (state : LoopSemState Word8 Unit) => state.locals 4) = some (some (.word 2))) &&
    -- LDiv by a zero divisor fails
    decide (loopArithSemHOL arithState8 (.div 4 2 8) = none) &&
    -- LLongMul: 3 * 2 = 6 (high 0, low 6)
    decide ((loopArithSemHOL arithState8 (.longMul 10 11 1 3)).map
      (fun (state : LoopSemState Word8 Unit) => state.locals 10) = some (some (.word 0))) &&
    decide ((loopArithSemHOL arithState8 (.longMul 10 11 1 3)).map
      (fun (state : LoopSemState Word8 Unit) => state.locals 11) = some (some (.word 6))) &&
    -- LLongDiv: (1 * 256 + 3) / 2 = 129, remainder 1
    decide ((loopArithSemHOL arithState8 (.longDiv 10 11 0 1 3)).map
      (fun (state : LoopSemState Word8 Unit) => state.locals 10) = some (some (.word 129))) &&
    decide ((loopArithSemHOL arithState8 (.longDiv 10 11 0 1 3)).map
      (fun (state : LoopSemState Word8 Unit) => state.locals 11) = some (some (.word 1))) &&
    -- LLongDiv overflow: (255 * 256 + 255) / 1 does not fit 8 bits
    decide (loopArithSemHOL arithState8 (.longDiv 10 11 5 6 7) = none)

#guard loopArithGuard

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
  let arithOk ← if loopArithGuard then
      IO.println "PASS Loop whole-state loop_arith exact port"
      pure true
    else
      IO.println "FAIL Loop whole-state loop_arith exact port"
      pure false
  pure (memoryOk && shMemOk && helpersOk && probeOk && arithOk)

end Flapjack.Test.LoopSemStateParity
