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

The canonical target also sets `ffiContext.sharedDomain` to the state's
`shMemaddrs` bitmap, matching HOL's `s.sh_memaddrs` shared-memory validity used
by `sh_mem_load`/`sh_mem_store`.

Direct oracle: `scripts/hol-probes/crep_runtime_shared_domain_probe.out`
  valid_zero_mem=T; valid_zero_out=F; valid_aligned_mem=T;
  valid_aligned_out=F; align_9=8w; align_16=16w

The external-call configuration/array arguments are read with HOL
`read_bytearray ptr (w2n len) (mem_load_byte s.memory s.memaddrs s.be)`; the
canonical target's `crepRuntimeReadBytes` is that byte list.

Direct oracle: `scripts/hol-probes/crep_runtime_read_bytes_probe.out`
  read_bytes_zero=SOME []; read_bytes_short=SOME [1w; 2w; 3w; 4w];
  read_bytes_cross=SOME [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w];
  read_bytes_out_of_domain=NONE
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
    ffiContext := riscv64PanValueFfiContext (fun _ => false)
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 0 }

def ffiProbeTarget : CrepRuntimeState (RiscV.Word 64) Unit :=
  riscv64CrepRuntimeTarget ffiProbeBase

/-- The canonical context the target installs on `ffiProbeBase`, with the base
    state's shared-memory bitmap as its `sharedDomain`. -/
def ffiProbeContext : PanValueFfiContext (RiscV.Word 64) :=
  riscv64PanValueFfiContext ffiProbeBase.shMemaddrs

/-- Bool mirror of the direct HOL oracle rows, evaluated by `#guard`. -/
def ffiByteCodecGuard : Bool :=
  (ffiProbeContext.byteAlign (9 : RiscV.Word 64) == (8 : RiscV.Word 64)) &&
  (ffiProbeContext.byteAlign (16 : RiscV.Word 64) == (16 : RiscV.Word 64)) &&
  (riscv64GetByte 0 oracleWord == (8 : UInt8)) &&
  (riscv64GetByte 1 oracleWord == (7 : UInt8)) &&
  (riscv64GetByte 7 oracleWord == (1 : UInt8)) &&
  (ffiProbeContext.wordToBytes oracleWord false ==
    [(8 : UInt8), 7, 6, 5, 4, 3, 2, 1]) &&
  (ffiProbeContext.wordOfBytes false
      (ffiProbeContext.wordToBytes oracleWord false) == oracleWord) &&
  (RiscV.panRiscVSetByte (8 : RiscV.Word 64) (0 : RiscV.Word 64)
      (RiscV.panRiscVGetByte (8 : RiscV.Word 64) (0 : RiscV.Word 64) oracleWord)
      oracleWord == oracleWord) &&
  (ffiProbeTarget.ffiContext.bigEndian == false) &&
  (ffiProbeTarget.ffiContext.byteAlign (9 : RiscV.Word 64) == (8 : RiscV.Word 64)) &&
  (ffiProbeTarget.ffiContext.wordToByte oracleWord == (8 : UInt8))

/-- A base state whose shared-memory bitmap is exactly the singleton `{8}`. -/
def ffiSharedBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { ffiProbeBase with shMemaddrs := fun address => address == 8 }

def ffiSharedTarget : CrepRuntimeState (RiscV.Word 64) Unit :=
  riscv64CrepRuntimeTarget ffiSharedBase

/-- Bool mirror of the shared-memory validity rows of the HOL oracle
    (`valid_zero_mem=T; valid_zero_out=F; valid_aligned_mem=T;
    valid_aligned_out=F; align_9=8w; align_16=16w`), where the canonical
    `ffiContext.sharedDomain` is the state's `shMemaddrs` bitmap. -/
def ffiSharedDomainGuard : Bool :=
  (crepRuntimeSharedAddressValid ffiSharedTarget .load (8 : RiscV.Word 64) == true) &&
  (crepRuntimeSharedAddressValid ffiSharedTarget .load (9 : RiscV.Word 64) == false) &&
  (crepRuntimeSharedAddressValid ffiSharedTarget .load32 (9 : RiscV.Word 64) == true) &&
  (crepRuntimeSharedAddressValid ffiSharedTarget .load32 (16 : RiscV.Word 64) == false) &&
  (crepRuntimeSharedAddressValid ffiSharedTarget .load32 (8 : RiscV.Word 64) == true) &&
  (ffiSharedTarget.ffiContext.sharedDomain (8 : RiscV.Word 64) == true) &&
  (ffiSharedTarget.ffiContext.sharedDomain (9 : RiscV.Word 64) == false) &&
  (RiscV.panRiscVByteAlign 8 (9 : RiscV.Word 64) == (8 : RiscV.Word 64)) &&
  (RiscV.panRiscVByteAlign 8 (16 : RiscV.Word 64) == (16 : RiscV.Word 64))

/-- The production target fixes `ffiContext` to the canonical byte codec, so the
    executable FFI boundary uses the HOL-shaped byte representation. -/
example : (riscv64CrepRuntimeTarget ffiProbeBase).ffiContext =
    ffiProbeContext :=
  riscv64CrepRuntimeTarget_ffiContext ffiProbeBase

/-- The canonical target's `sharedDomain` is the state's `shMemaddrs` bitmap. -/
example : (riscv64CrepRuntimeTarget ffiSharedBase).ffiContext.sharedDomain =
    ffiSharedBase.shMemaddrs := by
  funext address
  rw [riscv64CrepRuntimeTarget_sharedDomain]
  rfl

/-- A base state whose memory holds `0x0807060504030201` at address `8` and whose
    memory domain is `{8}`, matching the read-bytes oracle. -/
def ffiReadBase : CrepRuntimeState (RiscV.Word 64) Unit :=
  { ffiProbeBase with
    memory := fun address =>
      if address == (8 : RiscV.Word 64) then
        some (0x0807060504030201 : RiscV.Word 64)
      else none
    memaddrs := fun address => address == (8 : RiscV.Word 64) }

def ffiReadTarget : CrepRuntimeState (RiscV.Word 64) Unit :=
  riscv64CrepRuntimeTarget ffiReadBase

/-- Bool mirror of the read-bytes rows of the HOL oracle
    (`read_bytes_zero=SOME []; read_bytes_short=SOME [1w; 2w; 3w; 4w];
    read_bytes_cross=SOME [1w..8w]; read_bytes_out_of_domain=NONE`), where the
    production `crepRuntimeReadBytes` reads through the canonical target. -/
def ffiReadBytesGuard : Bool :=
  (crepRuntimeReadBytes ffiReadTarget (8 : RiscV.Word 64) 0 == some ([] : List UInt8)) &&
  (crepRuntimeReadBytes ffiReadTarget (8 : RiscV.Word 64) 4 ==
    some [(1 : UInt8), 2, 3, 4]) &&
  (crepRuntimeReadBytes ffiReadTarget (8 : RiscV.Word 64) 8 ==
    some [(1 : UInt8), 2, 3, 4, 5, 6, 7, 8]) &&
  (crepRuntimeReadBytes ffiReadTarget (8 : RiscV.Word 64) 9 == none) &&
  (riscv64ReadByteArray ffiReadBase (8 : RiscV.Word 64) 4 ==
    some [(1 : UInt8), 2, 3, 4])

/-- Production `crepRuntimeReadBytes` on the canonical target is the HOL
    `read_bytearray` byte list. -/
example : crepRuntimeReadBytes ffiReadTarget (8 : RiscV.Word 64) 4 =
    riscv64ReadByteArray ffiReadBase (8 : RiscV.Word 64) 4 :=
  crepRuntimeReadBytes_target_eq_riscv ffiReadBase 8 4

/-- The write-bytes oracle uses the same memory/domain as the read-bytes one. -/
def ffiWriteBase : CrepRuntimeState (RiscV.Word 64) Unit := ffiReadBase

def writeBytes8 : List UInt8 :=
  [(0xAA : UInt8), 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x11, 0x22]

def writeBytes1 : List UInt8 := [(0xAA : UInt8)]

/-- Bool mirror of the write-bytes rows of the HOL oracle
    (`write_head=SOME 0xAAw; write_byte1=SOME 0xBBw; write_32=SOME 0xDDCCBBAAw;
    write_unaligned_byte=SOME 0xAAw; write_out_of_domain=SOME 0x01w`), where
    `riscv64WriteMem` mirrors HOL's total `write_bytearray`. -/
def ffiWriteBytesGuard : Bool :=
  (RiscV.panRiscVReadByte ffiWriteBase.memaddrs
      (riscv64WriteMem ffiWriteBase (8 : RiscV.Word 64) writeBytes8)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (170 : RiscV.Word 64)) &&
  (RiscV.panRiscVReadByte ffiWriteBase.memaddrs
      (riscv64WriteMem ffiWriteBase (8 : RiscV.Word 64) writeBytes8)
      (8 : RiscV.Word 64) (9 : RiscV.Word 64) == some (187 : RiscV.Word 64)) &&
  (RiscV.panRiscVRead32 ffiWriteBase.memaddrs
      (riscv64WriteMem ffiWriteBase (8 : RiscV.Word 64) writeBytes8)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (0xDDCCBBAA : RiscV.Word 64)) &&
  (RiscV.panRiscVReadByte ffiWriteBase.memaddrs
      (riscv64WriteMem ffiWriteBase (9 : RiscV.Word 64) writeBytes1)
      (8 : RiscV.Word 64) (9 : RiscV.Word 64) == some (170 : RiscV.Word 64)) &&
  (RiscV.panRiscVReadByte ffiWriteBase.memaddrs
      (riscv64WriteMem ffiWriteBase (16 : RiscV.Word 64) writeBytes1)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) == some (1 : RiscV.Word 64))

/-- Production `crepRuntimeWriteBytes` on the canonical target maps to the HOL
    `write_bytearray` memory. -/
example : (crepRuntimeWriteBytes (riscv64CrepRuntimeTarget ffiWriteBase)
      (8 : RiscV.Word 64) writeBytes8).map (fun state => state.memory) =
    some (riscv64WriteMem ffiWriteBase (8 : RiscV.Word 64) writeBytes8) :=
  crepRuntimeWriteBytes_target_eq_riscv ffiWriteBase 8 writeBytes8

#guard ffiByteCodecGuard

#guard ffiSharedDomainGuard

#guard ffiReadBytesGuard

#guard ffiWriteBytesGuard

#eval ffiByteCodecGuard

#eval ffiSharedDomainGuard

#eval ffiReadBytesGuard

#eval ffiWriteBytesGuard

def runChecks : IO Bool := do
  if ffiByteCodecGuard then
    IO.println "PASS crep runtime RISC-V 64 FFI byte-codec target parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 FFI byte-codec target parity"
  if ffiSharedDomainGuard then
    IO.println "PASS crep runtime RISC-V 64 FFI shared-domain target parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 FFI shared-domain target parity"
  if ffiReadBytesGuard then
    IO.println "PASS crep runtime RISC-V 64 FFI read-bytes target parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 FFI read-bytes target parity"
  if ffiWriteBytesGuard then
    IO.println "PASS crep runtime RISC-V 64 FFI write-bytes target parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 FFI write-bytes target parity"
  pure (ffiByteCodecGuard && ffiSharedDomainGuard && ffiReadBytesGuard &&
    ffiWriteBytesGuard)

end Flapjack.Test.CrepRuntimeFfiTargetParity
