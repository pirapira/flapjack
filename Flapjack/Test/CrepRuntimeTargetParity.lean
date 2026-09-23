import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.RiscV.PanMemory

/-!
# Canonical RISC-V 64 Crep runtime target and word/byte memory boundary

`CrepRuntimeState` leaves `bytesInWord`, `memoryModel`, and `bigEndian`
unconstrained, unlike HOL `panSem$state` whose `bytes_in_word` is fixed by the
word type (`byte$bytes_in_word = n2w (dimindex (:'a) DIV 8)`) and whose
`mem_load_byte`/`mem_load_32` are fixed accordingly (panSemScript.sml:86-106).

This module adds a Flapjack-only canonical target instance that pins those
three fields to the RISC-V 64 values and connects the production runtime byte
load to the RISC-V model read. It is not a port of `stateRel` and it does not
change any tagged declaration; it fixes one production target operation
boundary without adding premises to a tagged theorem.

Direct oracle: `scripts/hol-probes/crep_runtime_word_boundary_probe.out`
  bytes64=8w; bytes32=4w; byte_at_9=SOME 2w; byte_at_8=SOME 1w;
  byte_outside_domain=NONE; word32_at_8=SOME 0x4030201w;
  word32_unaligned=NONE
-/

namespace Flapjack.Test.CrepRuntimeTargetParity

open Flapjack

/-- A minimal `PanValueFfiContext` for the 64-bit RISC-V target, used only to
    totalize the fixture state; it is not a claim about CakeML's FFI. -/
def riscv64FfiContext : PanValueFfiContext (RiscV.Word 64) :=
  { sharedDomain := fun _ => true
    byteAlign := fun address => address
    bigEndian := false
    wordToBytes := fun _ _ => []
    wordOfBytes := fun _ _ => 0
    wordToByte := fun value => UInt8.ofNat value.toNat
    byteToWord := fun value => BitVec.ofNat 64 value.toNat
    valueToNat := fun value => value.toNat }

/-- Canonical RISC-V 64 runtime target: fix the target word width and memory
    model, exactly the fields HOL leaves fixed by the target word type. -/
def riscv64CrepRuntimeTarget (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepRuntimeState (RiscV.Word 64) σ :=
  { base with
    bytesInWord := (8 : RiscV.Word 64)
    bigEndian := false
    memoryModel := RiscV.panRiscVMemoryModel }

/-- Predicate naming the canonical target constraints. -/
def isRiscV64CrepRuntimeTarget (state : CrepRuntimeState (RiscV.Word 64) σ) : Prop :=
  state.bytesInWord = (8 : RiscV.Word 64) ∧
    state.bigEndian = false ∧
    state.memoryModel = RiscV.panRiscVMemoryModel

theorem riscv64CrepRuntimeTarget_isTarget
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    isRiscV64CrepRuntimeTarget (riscv64CrepRuntimeTarget base) :=
  ⟨rfl, rfl, rfl⟩

/-- The canonical target fixes `bytesInWord` to the word-type value used by
    HOL `byte$bytes_in_word` (64 DIV 8 = 8). -/
theorem riscv64CrepRuntimeTarget_bytesInWord
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).bytesInWord = CrepBytesInWord.bytesInWord :=
  rfl

/-- On the canonical target the production Crep byte load is exactly the
    RISC-V model read that underlies HOL `mem_load_byte`. -/
theorem crepRuntimeLoadByte_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoadByte (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVReadByte base.memaddrs base.memory (8 : RiscV.Word 64) address :=
  rfl

/-! ## Concrete oracle fixture -/

def probeMemory : PanFlatMemory (RiscV.Word 64) :=
  fun address =>
    if address == (8 : RiscV.Word 64) then
      some (0x0807060504030201 : RiscV.Word 64)
    else none

def probeDomain : PanMemoryDomain (RiscV.Word 64) :=
  fun address => address == (8 : RiscV.Word 64)

def probeBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := probeMemory
    memaddrs := probeDomain
    shMemaddrs := fun _ => false
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := (8 : RiscV.Word 64)
    ffiContext := riscv64FfiContext
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def probeTargetState : CrepRuntimeState (RiscV.Word 64) Unit :=
  riscv64CrepRuntimeTarget probeBaseState

/-- Bool mirror of the seven HOL oracle rows, evaluated by `#guard`. -/
def wordBoundaryGuard : Bool :=
  (probeTargetState.bytesInWord == (8 : RiscV.Word 64)) &&
  (probeTargetState.bigEndian == false) &&
  ((8 : RiscV.Word 64) == CrepBytesInWord.bytesInWord) &&
  ((4 : RiscV.Word 32) == CrepBytesInWord.bytesInWord) &&
  (RiscV.panRiscVReadByte probeDomain probeMemory (8 : RiscV.Word 64) 9 ==
    some (0x02 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (9 : RiscV.Word 64) ==
    some (0x02 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (8 : RiscV.Word 64) ==
    some (0x01 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (16 : RiscV.Word 64)).isNone &&
  (crepRuntimeLoad32 probeTargetState (8 : RiscV.Word 64) ==
    some (0x04030201 : RiscV.Word 64)) &&
  (crepRuntimeLoad32 probeTargetState (9 : RiscV.Word 64)).isNone

#guard wordBoundaryGuard

#eval wordBoundaryGuard

def runChecks : IO Bool := do
  if wordBoundaryGuard then
    IO.println "PASS crep runtime RISC-V 64 target word/byte boundary parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 target word/byte boundary parity"
  pure wordBoundaryGuard

end Flapjack.Test.CrepRuntimeTargetParity
