import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.HolRef

/-!
# Loop `ExtCall` FFI boundary regression

Exercises `loopMachineExtCall`, the 64-bit RISC-V instance of the source
`ExtCall` case of `loopSem$evaluate_def` (`loopSemScript.sml:427-440`).

The observations are compared with the direct 64-bit HOL oracle
`scripts/hol-probes/loop_sem_ffi_rv64_probe.out`: it records intermediate
lookups, byte loads and byte-array reads, plus returned, terminal `FinalFFI`,
and malformed-local outcomes. The byte helpers `memLoadByteAuxHOL`,
`memStoreByteAuxHOL`, `readBytearrayHOL` and `writeBytearrayHOL` (in `LoopSem`)
are width-generic exact ports; the RV64 `ExtCall` executable path remains
untagged because HOL states the evaluator polymorphically.
-/

namespace Flapjack.Test.LoopFfiParity

open Flapjack

abbrev Word := RiscV.Word 64

def returningOracle : FfiOracle Unit :=
  fun _ _ _ _ => .returned () [0x11, 0x22]

def finalOracle : FfiOracle Unit :=
  fun _ _ _ _ => .final .failed

def returningState : FfiState Unit :=
  { oracle := returningOracle, state := (), ioEvents := [] }

def finalState : FfiState Unit :=
  { oracle := finalOracle, state := (), ioEvents := [] }

/-- Locals hold `ptr1 = 0`, `len1 = 1`, `ptr2 = 8`, `len2 = 2`; memory holds
    `0w -> 0xAB` and `8w -> 0xEFCD` (so the aligned bytes are `0xAB`, `0xCD`,
    `0xEF`), mirroring the HOL probe layout at 64 bits. -/
def baseState (ffi : FfiState Unit) : LoopMachineState Word Unit :=
  { locals := fun name =>
      match name with
      | 0 => some (.word (0 : Word))
      | 1 => some (.word (1 : Word))
      | 2 => some (.word (8 : Word))
      | 3 => some (.word (2 : Word))
      | _ => none
    globals := fun _ => none
    memory := fun address =>
      if address = (0 : Word) then some (.word (0xAB : Word))
      else if address = (8 : Word) then some (.word (0xEFCD : Word))
      else some (.word (0 : Word))
    mdomain := fun address => address = (0 : Word) || address = (8 : Word)
    shMdomain := fun _ => false
    clock := 100
    code := []
    be := false
    ffi := ffi
    baseAddr := 0
    topAddr := 0 }

/-- The successful returned call writes the oracle bytes at `8w` and `9w`
    (both align to `8w`), giving `0x2211`, and preserves the locals. -/
def returnedResult : LoopMachineStep Word Unit :=
  loopMachineExtCall (baseState returningState) "x" 0 1 2 3

/-- The terminal oracle result becomes `FinalFFI` and clears the locals. -/
def finalResult : LoopMachineStep Word Unit :=
  loopMachineExtCall (baseState finalState) "x" 0 1 2 3

/-- A configuration pointer that is not a live local yields `Error`. -/
def missingLocalResult : LoopMachineStep Word Unit :=
  loopMachineExtCall (baseState returningState) "x" 99 1 2 3

def returnedGuard : Bool :=
  match returnedResult.1 with
  | none =>
      returnedResult.2.memory (8 : Word) == some (.word (0x2211 : Word)) &&
      returnedResult.2.locals 1 == some (.word (1 : Word))
  | some _ => false

def finalGuard : Bool :=
  match finalResult.1, finalResult.2.locals 1 with
  | some (.finalFfi event), none =>
      event.name == .extCall "x" && event.configuration == [0xAB] &&
      event.bytes == [0xCD, 0xEF] && event.outcome == .failed
  | _, _ => false

def missingLocalGuard : Bool :=
  match missingLocalResult.1 with
  | some .error => true
  | _ => false

/-- `rv64_mem_load_byte_aux=(SOME 171w,SOME 205w,SOME 239w)`: the width-generic
    `memLoadByteAuxHOL` instance at 64 bits. -/
def memLoadGuard : Bool :=
  loopMemLoadByteAux (baseState returningState) 0 == some (0xAB : UInt8) &&
  loopMemLoadByteAux (baseState returningState) 8 == some (0xCD : UInt8) &&
  loopMemLoadByteAux (baseState returningState) 9 == some (0xEF : UInt8)

/-- `rv64_read_bytearrays=(SOME [171w],SOME [205w; 239w])`: the width-generic
    `readBytearrayHOL` fed by the 64-bit byte loader. -/
def readBytearrayGuard : Bool :=
  readBytearrayHOL (loopMemLoadByteAux (baseState returningState)) 0 1 ==
      some [0xAB] &&
  readBytearrayHOL (loopMemLoadByteAux (baseState returningState)) 8 2 ==
      some [0xCD, 0xEF]

/-- The width-generic `memStoreByteAuxHOL` replaces the aligned byte and leaves
    other words untouched (`0xEFCD` with byte 0 set to `0x11` is `0xEF11`). -/
def memStoreGuard : Bool :=
  let state := baseState returningState
  match memStoreByteAuxHOL (width := 64) state.memory state.mdomain state.be
      (8 : Word) 0x11 with
  | some memory =>
      memory (8 : Word) == some (.word (0xEF11 : Word)) &&
      memory (0 : Word) == some (.word (0xAB : Word))
  | none => false

/-- The width-generic `writeBytearrayHOL` writes the byte list in order at
    increasing addresses; the HOL probe records the result `0x2211` at `8w`. -/
def writeBytearrayGuard : Bool :=
  let state := baseState returningState
  let memory := writeBytearrayHOL (width := 64) state.memory state.mdomain
      state.be (8 : Word) [0x11, 0x22]
  memory (8 : Word) == some (.word (0x2211 : Word))

#guard returnedGuard
#guard finalGuard
#guard missingLocalGuard
#guard memLoadGuard
#guard readBytearrayGuard
#guard memStoreGuard
#guard writeBytearrayGuard

def runChecks : IO Bool := do
  let returnedOk ←
    if returnedGuard then
      IO.println "PASS Loop ExtCall returned writes bytes and preserves locals"
      pure true
    else
      IO.println "FAIL Loop ExtCall returned writes bytes and preserves locals"
      pure false
  let finalOk ←
    if finalGuard then
      IO.println "PASS Loop ExtCall final yields FinalFFI and clears locals"
      pure true
    else
      IO.println "FAIL Loop ExtCall final yields FinalFFI and clears locals"
      pure false
  let missingOk ←
    if missingLocalGuard then
      IO.println "PASS Loop ExtCall missing local errors"
      pure true
    else
      IO.println "FAIL Loop ExtCall missing local errors"
      pure false
  let memLoadOk ←
    if memLoadGuard then
      IO.println "PASS Loop width-generic mem_load_byte_aux byte loads"
      pure true
    else
      IO.println "FAIL Loop width-generic mem_load_byte_aux byte loads"
      pure false
  let readBytearrayOk ←
    if readBytearrayGuard then
      IO.println "PASS Loop width-generic read_bytearray byte-array reads"
      pure true
    else
      IO.println "FAIL Loop width-generic read_bytearray byte-array reads"
      pure false
  let memStoreOk ←
    if memStoreGuard then
      IO.println "PASS Loop width-generic mem_store_byte_aux byte store"
      pure true
    else
      IO.println "FAIL Loop width-generic mem_store_byte_aux byte store"
      pure false
  let writeBytearrayOk ←
    if writeBytearrayGuard then
      IO.println "PASS Loop width-generic write_bytearray byte-array writes"
      pure true
    else
      IO.println "FAIL Loop width-generic write_bytearray byte-array writes"
      pure false
  pure (returnedOk && finalOk && missingOk && memLoadOk && readBytearrayOk &&
    memStoreOk && writeBytearrayOk)

end Flapjack.Test.LoopFfiParity
