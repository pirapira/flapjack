import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-!
# Canonical RISC-V 64 Crep FFI byte-codec boundary

The canonical target's `ffiContext` and its bridges live in the production
module `Flapjack.Pancake.Semantics.CrepRuntimeTarget`; this module exercises
them against the direct HOL oracle.

`crepRuntimeReadBytes`/`crepRuntimeWriteBytes`/`crepRuntimeExtCallValues` and
`crepRuntimeSharedMem` take the byte image of a machine word from
`CrepRuntimeState.ffiContext` and hand it to the external handler, mirroring the
byte list HOL `call_FFI` receives from `byte$word_to_bytes`. HOL's byte
functions use `get_byte`, `set_byte`, and `byte_align` with
`byte$bytes_in_word = n2w (dimindex (:'a) DIV 8)` (byteScript.sml,
alignmentScript.sml); the canonical context uses the RISC-V helpers with the
same offset arithmetic.

Direct oracle: `scripts/hol-probes/crep_runtime_ffi_boundary_probe.out`
  bytes64=8w; get_byte_0=8w; get_byte_1=7w; get_byte_7=1w; byte_align_8=8w;
  byte_align_16=16w; word_to_bytes_64=[8w; 7w; 6w; 5w; 4w; 3w; 2w; 1w];
  word_of_bytes_roundtrip=0x102030405060708w; set_byte_0_roundtrip=0x102030405060708w
-/

namespace Flapjack.Test.CrepRuntimeFfiTargetParity

open Flapjack

/-- The 64-bit word whose little-endian byte image the oracle prints. -/
def oracleWord : RiscV.Word 64 := 0x0102030405060708

/-- A minimal base state, only used to run `riscv64CrepRuntimeTarget`. -/
def ffiProbeBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := FEMPTY
    memory := fun _ => none
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := (8 : RiscV.Word 64)
    ffiContext := riscv64PanValueFfiContext
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def ffiProbeTarget : CrepRuntimeState (RiscV.Word 64) Unit :=
  riscv64CrepRuntimeTarget ffiProbeBase

/-- Bool mirror of the direct HOL oracle rows, evaluated by `#guard`. -/
def ffiByteCodecGuard : Bool :=
  (riscv64PanValueFfiContext.byteAlign (9 : RiscV.Word 64) == (8 : RiscV.Word 64)) &&
  (riscv64PanValueFfiContext.byteAlign (16 : RiscV.Word 64) == (16 : RiscV.Word 64)) &&
  (riscv64GetByte 0 oracleWord == (8 : UInt8)) &&
  (riscv64GetByte 1 oracleWord == (7 : UInt8)) &&
  (riscv64GetByte 7 oracleWord == (1 : UInt8)) &&
  (riscv64PanValueFfiContext.wordToBytes oracleWord false ==
    [(8 : UInt8), 7, 6, 5, 4, 3, 2, 1]) &&
  (riscv64PanValueFfiContext.wordOfBytes false
      (riscv64PanValueFfiContext.wordToBytes oracleWord false) == oracleWord) &&
  (RiscV.panRiscVSetByte (8 : RiscV.Word 64) (0 : RiscV.Word 64)
      (RiscV.panRiscVGetByte (8 : RiscV.Word 64) (0 : RiscV.Word 64) oracleWord)
      oracleWord == oracleWord) &&
  (ffiProbeTarget.ffiContext.bigEndian == false) &&
  (ffiProbeTarget.ffiContext.byteAlign (9 : RiscV.Word 64) == (8 : RiscV.Word 64)) &&
  (ffiProbeTarget.ffiContext.wordToByte oracleWord == (8 : UInt8))

/-- The production target fixes `ffiContext` to the canonical byte codec, so the
    executable FFI boundary uses the HOL-shaped byte representation. -/
example : (riscv64CrepRuntimeTarget ffiProbeBase).ffiContext =
    riscv64PanValueFfiContext :=
  riscv64CrepRuntimeTarget_ffiContext ffiProbeBase

#guard ffiByteCodecGuard

#eval ffiByteCodecGuard

def runChecks : IO Bool := do
  if ffiByteCodecGuard then
    IO.println "PASS crep runtime RISC-V 64 FFI byte-codec target parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 FFI byte-codec target parity"
  pure ffiByteCodecGuard

end Flapjack.Test.CrepRuntimeFfiTargetParity
