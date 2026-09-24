import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-!
# Canonical RISC-V 64 Crep runtime target and word/byte memory boundary

The canonical target and its production bridges live in the production module
`Flapjack.Pancake.Semantics.CrepRuntimeTarget`; this module exercises them
against the direct HOL oracle.

`CrepRuntimeState` leaves `bytesInWord`, `memoryModel`, and `bigEndian`
unconstrained, unlike HOL `panSem$state` whose `bytes_in_word` is fixed by the
word type (`byte$bytes_in_word = n2w (dimindex (:'a) DIV 8)`) and whose
`mem_load_byte`/`mem_load_32` are fixed accordingly (panSemScript.sml:86-106).

Direct oracle: `scripts/hol-probes/crep_runtime_word_boundary_probe.out`
  bytes64=8w; bytes32=4w; byte_at_9=SOME 2w; byte_at_8=SOME 1w;
  byte_outside_domain=NONE; word32_at_8=SOME 0x4030201w;
  word32_unaligned=NONE; store_byte_roundtrip=SOME 0xABw;
  store_byte_outside=NONE; store32_roundtrip=SOME 0xAABBCCDDw;
  store32_unaligned=NONE; store32_outside=NONE
-/

namespace Flapjack.Test.CrepRuntimeTargetParity

open Flapjack

/-! ## Concrete oracle fixture -/

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

def probeMemory : RiscV.Word 64 → PanWordLab (RiscV.Word 64) :=
  fun address =>
    if address == (8 : RiscV.Word 64) then
      .word (0x0807060504030201 : RiscV.Word 64)
    else .word 0

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

/-- Bool mirror of the direct HOL oracle rows, evaluated by `#guard`. -/
def wordBoundaryGuard : Bool :=
  (probeTargetState.bytesInWord == (8 : RiscV.Word 64)) &&
  (probeTargetState.bigEndian == false) &&
  ((8 : RiscV.Word 64) == CrepBytesInWord.bytesInWord) &&
  ((4 : RiscV.Word 32) == CrepBytesInWord.bytesInWord) &&
  (RiscV.panRiscVReadByte probeDomain (crepRuntimeMemoryView probeMemory) (8 : RiscV.Word 64) 9 ==
    some (0x02 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (9 : RiscV.Word 64) ==
    some (0x02 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (8 : RiscV.Word 64) ==
    some (0x01 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte probeTargetState (16 : RiscV.Word 64)).isNone &&
  (crepRuntimeLoad32 probeTargetState (8 : RiscV.Word 64) ==
    some (0x04030201 : RiscV.Word 64)) &&
  (crepRuntimeLoad32 probeTargetState (9 : RiscV.Word 64)).isNone

/-- Memory cell read back from a store result. -/
def storedMemoryAt (result : Option (CrepRuntimeState (RiscV.Word 64) Unit))
    (address : RiscV.Word 64) : Option (RiscV.Word 64) :=
  result.bind (fun state => crepRuntimeMemoryView state.memory address)

/-- Word/byte store round-trips through the canonical target: the production
    store updates the same cell the RISC-V model store does, and rejects
    out-of-domain addresses. -/
def storeRoundTripGuard : Bool :=
  (storedMemoryAt (crepRuntimeStore probeTargetState (8 : RiscV.Word 64)
      (0xAB : RiscV.Word 64)) (8 : RiscV.Word 64) == some (0xAB : RiscV.Word 64)) &&
  (storedMemoryAt (crepRuntimeStoreByte probeTargetState (8 : RiscV.Word 64)
      (0xAB : RiscV.Word 64)) (8 : RiscV.Word 64) ==
    some (0x08070605040302AB : RiscV.Word 64)) &&
  (storedMemoryAt (crepRuntimeStore32 probeTargetState (8 : RiscV.Word 64)
      (0xAABBCCDD : RiscV.Word 64)) (8 : RiscV.Word 64) ==
    some (0x08070605AABBCCDD : RiscV.Word 64)) &&
  (crepRuntimeStore probeTargetState (16 : RiscV.Word 64)
      (0xAB : RiscV.Word 64)).isNone &&
  (crepRuntimeStoreByte probeTargetState (16 : RiscV.Word 64)
      (0xAB : RiscV.Word 64)).isNone &&
  (crepRuntimeStore32 probeTargetState (9 : RiscV.Word 64)
      (0xAABBCCDD : RiscV.Word 64)).isNone &&
  (crepRuntimeStore32 probeTargetState (16 : RiscV.Word 64)
      (0xAABBCCDD : RiscV.Word 64)).isNone &&
  ((crepRuntimeStore32 probeTargetState (8 : RiscV.Word 64)
      (0xAABBCCDD : RiscV.Word 64)).bind (fun state => crepRuntimeMemoryView state.memory (8 : RiscV.Word 64)) ==
    (RiscV.panRiscVStore32 probeDomain (crepRuntimeMemoryView probeMemory) (8 : RiscV.Word 64)
      (8 : RiscV.Word 64) (0xAABBCCDD : RiscV.Word 64)).bind
        (fun memory => memory (8 : RiscV.Word 64)))

/-- The production evaluator computes `.load`/`.load32` through the same model
    operations the canonical target bridges expose. -/
example : crepRuntimeLoad (riscv64CrepRuntimeTarget probeBaseState) (8 : RiscV.Word 64) =
    RiscV.panRiscVReadWord probeBaseState.memaddrs (crepRuntimeMemoryView probeBaseState.memory)
      (8 : RiscV.Word 64) :=
  crepRuntimeLoad_target_eq_riscv probeBaseState 8

example : crepRuntimeLoad32 (riscv64CrepRuntimeTarget probeBaseState) (8 : RiscV.Word 64) =
    RiscV.panRiscVRead32 probeBaseState.memaddrs (crepRuntimeMemoryView probeBaseState.memory)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) :=
  crepRuntimeLoad32_target_eq_riscv probeBaseState 8

/-- The 32-bit store production path is the same memory update as
    `panModelStore32` on the canonical target. -/
example : (crepRuntimeStore32 (riscv64CrepRuntimeTarget probeBaseState)
      (8 : RiscV.Word 64) (0xAABBCCDD : RiscV.Word 64)).map (fun state => crepRuntimeMemoryView state.memory) =
    RiscV.panRiscVStore32 probeBaseState.memaddrs (crepRuntimeMemoryView probeBaseState.memory)
      (8 : RiscV.Word 64) (8 : RiscV.Word 64) (0xAABBCCDD : RiscV.Word 64) :=
  crepRuntimeStore32_target_eq_riscv probeBaseState 8 (0xAABBCCDD : RiscV.Word 64)

/-! ## Configuration stability through production transitions -/

example : isRiscV64CrepRuntimeTarget (riscv64CrepRuntimeTarget probeBaseState) :=
  riscv64CrepRuntimeTarget_isTarget probeBaseState

example : isRiscV64CrepRuntimeTarget
    (clearCrepRuntimeLocals (riscv64CrepRuntimeTarget probeBaseState)) :=
  isRiscV64CrepRuntimeTarget_clearCrepRuntimeLocals
    (riscv64CrepRuntimeTarget_isTarget probeBaseState)

example : isRiscV64CrepRuntimeTarget
    (decCrepClock (riscv64CrepRuntimeTarget probeBaseState)) :=
  isRiscV64CrepRuntimeTarget_decCrepClock
    (riscv64CrepRuntimeTarget_isTarget probeBaseState)

example : isRiscV64CrepRuntimeTarget
    (riscv64WriteState probeBaseState (8 : RiscV.Word 64) [1, 2]) :=
  isRiscV64CrepRuntimeTarget_riscv64WriteState probeBaseState 8 [1, 2]

example : isRiscV64CrepRuntimeTarget
    (crepRuntimeSharedMem
      (riscv64SharedMemCallFfiHandler :
        CrepRuntimeFfiHandler (RiscV.Word 64) Unit FfiFinalEvent)
      (riscv64CrepRuntimeTarget probeBaseState) .load 0 (8 : RiscV.Word 64)).2 :=
  isRiscV64CrepRuntimeTarget_crepRuntimeSharedMem
    (riscv64SharedMemCallFfiHandler :
      CrepRuntimeFfiHandler (RiscV.Word 64) Unit FfiFinalEvent)
    .load 0 (8 : RiscV.Word 64) (riscv64CrepRuntimeTarget_isTarget probeBaseState)

example : isRiscV64CrepRuntimeTarget
    (crepRuntimeExtCall
      (riscv64SharedMemCallFfiHandler :
        CrepRuntimeFfiHandler (RiscV.Word 64) Unit FfiFinalEvent)
      (riscv64CrepRuntimeTarget probeBaseState) "f" 0 1 2 3).2 :=
  isRiscV64CrepRuntimeTarget_crepRuntimeExtCall
    (riscv64SharedMemCallFfiHandler :
      CrepRuntimeFfiHandler (RiscV.Word 64) Unit FfiFinalEvent)
    "f" 0 1 2 3 (riscv64CrepRuntimeTarget_isTarget probeBaseState)

/-! ## HOL `LoadByte` evaluator-case bridge oracle

Direct oracle: `scripts/hol-probes/crep_eval_load_byte_probe.out`
  eval_loadbyte_addr8=SOME (Word 136w); eval_loadbyte_addr9=SOME (Word 119w);
  eval_loadbyte_addr10=SOME (Word 102w); eval_loadbyte_outside_domain=NONE;
  mem_load_byte_addr9=SOME 119w
-/

def loadByteMemory : RiscV.Word 64 → PanWordLab (RiscV.Word 64) :=
  fun address =>
    if address == (8 : RiscV.Word 64) then
      .word (0x1122334455667788 : RiscV.Word 64)
    else .word 0

def loadByteBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { probeBaseState with memory := loadByteMemory }

/-- The production `LoadByte` and word_lab evaluator cases at the RV64 target
match the direct HOL `mem_load_byte` oracle rows (little-endian byte extraction
plus the memaddrs guard). -/
def loadByteEvalGuard : Bool :=
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.loadByte (.const (8 : RiscV.Word 64))) ==
    some (.word (136 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.loadByte (.const (9 : RiscV.Word 64))) ==
    some (.word (119 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.loadByte (.const (10 : RiscV.Word 64))) ==
    some (.word (102 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.loadByte (.const (16 : RiscV.Word 64)))).isNone &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.loadByte (.const (8 : RiscV.Word 64))) ==
    some (136 : RiscV.Word 64)) &&
  (holMemLoadByte64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) false (9 : RiscV.Word 64) ==
    some (119 : RiscV.Word 64)) &&
  (crepRuntimeLoadByte (riscv64CrepRuntimeTarget loadByteBaseState) (8 : RiscV.Word 64) ==
    holMemLoadByte64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) false (8 : RiscV.Word 64))

/-- The genuine evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.loadByte (.const (9 : RiscV.Word 64))) =
      (holMemLoadByte64 loadByteBaseState.memaddrs
        (crepRuntimeMemoryView loadByteBaseState.memory) false (9 : RiscV.Word 64)).map
          PanWordLab.word :=
  evalCrepRuntimeExpWordLab_loadByte_rv64_const loadByteBaseState (9 : RiscV.Word 64)

#guard wordBoundaryGuard
#guard storeRoundTripGuard
#guard loadByteEvalGuard

#eval wordBoundaryGuard
#eval storeRoundTripGuard
#eval loadByteEvalGuard

/-- The production `Load32` and word_lab evaluator cases at the RV64 target
match the direct HOL `mem_load_32` oracle rows: little-endian four-byte reads,
the alignment guard, and the memaddrs domain guard.  The primitive-byte-order
checks distinguish little- from big-endian composition. -/
def load32EvalGuard : Bool :=
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load32 (.const (8 : RiscV.Word 64))) ==
    some (.word (0x55667788 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load32 (.const (12 : RiscV.Word 64))) ==
    some (.word (0x11223344 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load32 (.const (9 : RiscV.Word 64)))).isNone &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load32 (.const (24 : RiscV.Word 64)))).isNone &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load32 (.const (8 : RiscV.Word 64))) ==
    some (0x55667788 : RiscV.Word 64)) &&
  (holMemLoad32_64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) false (8 : RiscV.Word 64) ==
    some (0x55667788 : RiscV.Word 64)) &&
  (holMemLoad32_64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) true (8 : RiscV.Word 64) ==
    some (0x11223344 : RiscV.Word 64)) &&
  (crepRuntimeLoad32 (riscv64CrepRuntimeTarget loadByteBaseState) (8 : RiscV.Word 64) ==
    holMemLoad32_64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) false (8 : RiscV.Word 64))

/-- The genuine evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.load32 (.const (8 : RiscV.Word 64))) =
      (holMemLoad32_64 loadByteBaseState.memaddrs
        (crepRuntimeMemoryView loadByteBaseState.memory) false (8 : RiscV.Word 64)).map
          PanWordLab.word :=
  evalCrepRuntimeExpWordLab_load32_rv64_const loadByteBaseState (8 : RiscV.Word 64)

#guard load32EvalGuard

#eval load32EvalGuard

/-- Oracle guard for the plain word-cell `Load` evaluator case against the direct
HOL `mem_load` probe rows: the valid cell at address 8 returns the wrapped
64-bit word, and an address outside `memaddrs` returns none. -/
def loadEvalGuard : Bool :=
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load (.const (8 : RiscV.Word 64))) ==
    some (.word (0x1122334455667788 : RiscV.Word 64))) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load (.const (9 : RiscV.Word 64)))).isNone &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.load (.const (8 : RiscV.Word 64))) ==
    some (0x1122334455667788 : RiscV.Word 64)) &&
  (holMemLoad64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) (8 : RiscV.Word 64) ==
    some (0x1122334455667788 : RiscV.Word 64)) &&
  (holMemLoad64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) (9 : RiscV.Word 64)).isNone &&
  (crepRuntimeLoad (riscv64CrepRuntimeTarget loadByteBaseState) (8 : RiscV.Word 64) ==
    holMemLoad64 loadByteBaseState.memaddrs
      (crepRuntimeMemoryView loadByteBaseState.memory) (8 : RiscV.Word 64))

/-- The genuine word-cell evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.load (.const (8 : RiscV.Word 64))) =
      (holMemLoad64 loadByteBaseState.memaddrs
        (crepRuntimeMemoryView loadByteBaseState.memory) (8 : RiscV.Word 64)).map
          PanWordLab.word :=
  evalCrepRuntimeExpWordLab_load_rv64_const loadByteBaseState (8 : RiscV.Word 64)

#guard loadEvalGuard

#eval loadEvalGuard

/-- The RV64 `Op` evaluator case over constant operands.  Oracle rows
`scripts/hol-probes/crep_eval_op_rv64_probe.out`: Add 3+4=7, Sub 7-2=5,
And 0xF0&0x3C=0x30, empty Add=0, Sub with one operand fails. -/
def opEvalGuard : Bool :=
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .add [.const (3 : RiscV.Word 64), .const (4 : RiscV.Word 64)]) ==
    some (7 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .sub [.const (7 : RiscV.Word 64), .const (2 : RiscV.Word 64)]) ==
    some (5 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .and [.const (0xF0 : RiscV.Word 64), .const (0x3C : RiscV.Word 64)]) ==
    some (0x30 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .add ([] : List (CrepExp (RiscV.Word 64)))) ==
    some (0 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .sub [.const (7 : RiscV.Word 64)])).isNone &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.op .add [.const (3 : RiscV.Word 64), .const (4 : RiscV.Word 64)]) ==
    some (.word (7 : RiscV.Word 64)))

/-- The genuine RV64 `Op` evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.op .add [.const (3 : RiscV.Word 64), .const (4 : RiscV.Word 64)]) =
      (wordOpHOL .add [(3 : RiscV.Word 64), (4 : RiscV.Word 64)]).map
        PanWordLab.word :=
  evalCrepRuntimeExpWordLab_op_rv64_const loadByteBaseState .add
    [(3 : RiscV.Word 64), (4 : RiscV.Word 64)]

#guard opEvalGuard

#eval opEvalGuard

/-- The RV64 `Cmp` evaluator case over constant operands.  Oracle rows
`scripts/hol-probes/crep_eval_cmp_rv64_probe.out`: Equal 5 5 -> 1, Equal 5 6 -> 0,
Lower 3 5 -> 1, Test 0xF0 0x10 -> 0, Test 0xF0 0x0F -> 1. -/
def cmpEvalGuard : Bool :=
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .equal (.const (5 : RiscV.Word 64)) (.const (5 : RiscV.Word 64))) ==
    some (1 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .equal (.const (5 : RiscV.Word 64)) (.const (6 : RiscV.Word 64))) ==
    some (0 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .lower (.const (3 : RiscV.Word 64)) (.const (5 : RiscV.Word 64))) ==
    some (1 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .test (.const (0xF0 : RiscV.Word 64)) (.const (0x10 : RiscV.Word 64))) ==
    some (0 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .test (.const (0xF0 : RiscV.Word 64)) (.const (0x0F : RiscV.Word 64))) ==
    some (1 : RiscV.Word 64)) &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.cmp .equal (.const (5 : RiscV.Word 64)) (.const (5 : RiscV.Word 64))) ==
    some (.word (1 : RiscV.Word 64)))

/-- The genuine RV64 `Cmp` evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.cmp .equal (.const (5 : RiscV.Word 64)) (.const (5 : RiscV.Word 64))) =
      some (.word (RiscV.panRiscVCmp .equal (5 : RiscV.Word 64) (5 : RiscV.Word 64))) :=
  evalCrepRuntimeExpWordLab_cmp_rv64_const loadByteBaseState .equal
    (5 : RiscV.Word 64) (5 : RiscV.Word 64)

#guard cmpEvalGuard

#eval cmpEvalGuard

/-- HOL `word_sh` over the constant-operand RV64 oracle rows: Lsl/Lsr/Asr/Ror,
amount zero valid, width-sized amount invalid. -/
def shiftEvalGuard : Bool :=
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .lsl (.const (1 : RiscV.Word 64)) (.const (3 : RiscV.Word 64))) ==
    some (8 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .lsr (.const (16 : RiscV.Word 64)) (.const (2 : RiscV.Word 64))) ==
    some (4 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .asr (.const (0x8000000000000000 : RiscV.Word 64)) (.const (4 : RiscV.Word 64))) ==
    some (0xF800000000000000 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .ror (.const (1 : RiscV.Word 64)) (.const (1 : RiscV.Word 64))) ==
    some (0x8000000000000000 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .lsl (.const (7 : RiscV.Word 64)) (.const (0 : RiscV.Word 64))) ==
    some (7 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .lsl (.const (7 : RiscV.Word 64)) (.const (64 : RiscV.Word 64)))).isNone &&
  (holWordShift64 .lsl (1 : RiscV.Word 64) 3 == some (8 : RiscV.Word 64)) &&
  (holWordShift64 .asr (0x8000000000000000 : RiscV.Word 64) 4 ==
    some (0xF800000000000000 : RiscV.Word 64)) &&
  (holWordShift64 .lsl (7 : RiscV.Word 64) 64).isNone &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.shift .lsl (.const (1 : RiscV.Word 64)) (.const (3 : RiscV.Word 64))) ==
    some (.word (8 : RiscV.Word 64)))

/-- The genuine RV64 `Shift` evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.shift .lsl (.const (1 : RiscV.Word 64)) (.const (3 : RiscV.Word 64))) =
      (holWordShift64 .lsl (1 : RiscV.Word 64) 3).map
        PanWordLab.word :=
  evalCrepRuntimeExpWordLab_shift_rv64_const loadByteBaseState .lsl
    (1 : RiscV.Word 64) (3 : RiscV.Word 64)

#guard shiftEvalGuard

#eval shiftEvalGuard

/-- Oracle rows for the RV64 `Crepop Mul` evaluator case against HOL `crep_op`. -/
def crepOpEvalGuard : Bool :=
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [.const (6 : RiscV.Word 64), .const (7 : RiscV.Word 64)]) ==
    some (42 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [.const (5 : RiscV.Word 64), .const (6 : RiscV.Word 64)]) ==
    some (30 : RiscV.Word 64)) &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [.const (2 : RiscV.Word 64), .const (3 : RiscV.Word 64),
        .const (4 : RiscV.Word 64)])).isNone &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [.const (2 : RiscV.Word 64)])).isNone &&
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [])).isNone &&
  (holCrepOpMul64 [(6 : RiscV.Word 64), (7 : RiscV.Word 64)] ==
    some (42 : RiscV.Word 64)) &&
  (holCrepOpMul64 [(2 : RiscV.Word 64), (3 : RiscV.Word 64),
    (4 : RiscV.Word 64)]).isNone &&
  (evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
      (.crepOp .mul [.const (6 : RiscV.Word 64), .const (7 : RiscV.Word 64)]) ==
    some (.word (42 : RiscV.Word 64)))

/-- The genuine RV64 `Crepop Mul` evaluator-case bridge instantiated at the oracle fixture. -/
example :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget loadByteBaseState)
        (.crepOp .mul [.const (6 : RiscV.Word 64), .const (7 : RiscV.Word 64)]) =
      (holCrepOpMul64 [(6 : RiscV.Word 64), (7 : RiscV.Word 64)]).map
        PanWordLab.word :=
  evalCrepRuntimeExpWordLab_crepOpMul_rv64_const loadByteBaseState
    [(6 : RiscV.Word 64), (7 : RiscV.Word 64)]

#guard crepOpEvalGuard

#eval crepOpEvalGuard

/-! ## All-expression evaluator correspondence with the HOL-shaped reference -/

/-- RV64 locals with two word variables, so correspondence can be checked on
    non-constant operands. -/
def corrLocals : Nat → Option (PanWordLab (RiscV.Word 64)) :=
  fun name =>
    if name == 1 then some (.word (5 : RiscV.Word 64))
    else if name == 2 then some (.word (3 : RiscV.Word 64)) else none

def corrState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { probeBaseState with locals := corrLocals }

/-- The production RV64 evaluator read through `PanWordLab.word` equals the
    HOL-shaped reference evaluator on compound, non-constant expressions. -/
def corrGuard : Bool :=
  (evalCrepRuntimeExp (riscv64CrepRuntimeTarget corrState)
      (.op .add [.var 1, .var 2])).map PanWordLab.word ==
      holCrepEval64 corrState (.op .add [.var 1, .var 2]) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget corrState)
      (.cmp .lower (.var 1) (.var 2))).map PanWordLab.word ==
      holCrepEval64 corrState (.cmp .lower (.var 1) (.var 2)) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget corrState)
      (.shift .lsl (.var 2) (.var 2))).map PanWordLab.word ==
      holCrepEval64 corrState (.shift .lsl (.var 2) (.var 2)) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget corrState)
      (.crepOp .mul [.var 1, .var 2])).map PanWordLab.word ==
      holCrepEval64 corrState (.crepOp .mul [.var 1, .var 2])

example :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget corrState)
        (.op .add [.var 1, .var 2])).map PanWordLab.word =
      holCrepEval64 corrState (.op .add [.var 1, .var 2]) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 corrState _

#guard corrGuard
#eval corrGuard

/-! ## Arbitrary Shift hook versus HOL `word_sh` -/

/-- A memory model whose `shift` hook is literally HOL `word_sh` at 64 bits,
    but which is otherwise not the RISC-V target model. -/
def holShiftModel : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with
    shift := fun operator left right => holWordShift64 operator left right.toNat }

def holShiftBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { probeBaseState with memoryModel := holShiftModel }

theorem holShiftBaseState_matches :
    CrepMemoryModelShiftMatchesHOL64 holShiftBaseState.memoryModel :=
  fun _ _ _ => rfl

example : CrepMemoryModelShiftMatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_shift_matches_HOL64 corrState

example :
    evalCrepRuntimeExp holShiftBaseState (.shift .lsl (.const 1) (.const 3)) =
      holWordShift64 .lsl 1 3 :=
  evalCrepRuntimeExp_shift_const_of_matches holShiftBaseState
    holShiftBaseState_matches .lsl 1 3

/-- The production evaluator over an arbitrary matching model agrees with HOL
    `word_sh` on valid shifts and rejects an out-of-range amount. -/
def shiftMatchesGuard : Bool :=
  (evalCrepRuntimeExp holShiftBaseState (.shift .lsl (.const 1) (.const 3)) ==
      some (8 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holShiftBaseState (.shift .lsl (.const 1) (.const 64)) ==
      none) &&
    (evalCrepRuntimeExp holShiftBaseState (.shift .ror (.const 1) (.const 1)) ==
      some (0x8000000000000000 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holShiftBaseState)
        (.shift .lsl (.const 1) (.const 3)) == some (8 : RiscV.Word 64))

#guard shiftMatchesGuard
#eval shiftMatchesGuard

/-- A memory model whose `wordOp` hook is literally HOL `word_op` at 64 bits,
    but which is otherwise not the RISC-V target model. -/
def holOpModel : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with wordOp := fun operator values => wordOpHOL operator values }

def holOpBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { probeBaseState with memoryModel := holOpModel }

theorem holOpBaseState_matches :
    CrepMemoryModelOpMatchesHOL64 holOpBaseState.memoryModel :=
  fun _ _ => rfl

example : CrepMemoryModelOpMatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_op_matches_HOL64 corrState

example :
    evalCrepRuntimeExp holOpBaseState
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) =
      wordOpHOL .add [3, 4] :=
  evalCrepRuntimeExp_op_const_of_matches holOpBaseState holOpBaseState_matches .add [3, 4]

/-- The production evaluator over an arbitrary matching model agrees with HOL
    `word_op` on valid operations and rejects an out-of-range arity. -/
def opMatchesGuard : Bool :=
  (evalCrepRuntimeExp holOpBaseState
      (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) ==
    some (7 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holOpBaseState
        (.op .and ([(0xF0 : RiscV.Word 64), 0x3C].map CrepExp.const)) ==
      some (0x30 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holOpBaseState
        (.op .sub ([(7 : RiscV.Word 64)].map CrepExp.const)) ==
      none) &&
    (evalCrepRuntimeExpWordLab holOpBaseState
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) ==
      some (.word (7 : RiscV.Word 64))) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holOpBaseState)
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) ==
      some (7 : RiscV.Word 64))

#guard opMatchesGuard
#eval opMatchesGuard

def runChecks : IO Bool := do
  if wordBoundaryGuard && storeRoundTripGuard then
    IO.println "PASS crep runtime RISC-V 64 target word/byte boundary parity"
  else
    IO.println "FAIL crep runtime RISC-V 64 target word/byte boundary parity"
  if loadByteEvalGuard then
    IO.println "PASS crep LoadByte evaluator case matches HOL mem_load_byte oracle"
  else
    IO.println "FAIL crep LoadByte evaluator case matches HOL mem_load_byte oracle"
  if load32EvalGuard then
    IO.println "PASS crep Load32 evaluator case matches HOL mem_load_32 oracle"
  else
    IO.println "FAIL crep Load32 evaluator case matches HOL mem_load_32 oracle"
  if loadEvalGuard then
    IO.println "PASS crep Load evaluator case matches HOL mem_load oracle"
  else
    IO.println "FAIL crep Load evaluator case matches HOL mem_load oracle"
  if opEvalGuard then
    IO.println "PASS crep Op evaluator case matches HOL word_op oracle"
  else
    IO.println "FAIL crep Op evaluator case matches HOL word_op oracle"
  if cmpEvalGuard then
    IO.println "PASS crep Cmp evaluator case matches HOL word_cmp oracle"
  else
    IO.println "FAIL crep Cmp evaluator case matches HOL word_cmp oracle"
  if shiftEvalGuard then
    IO.println "PASS crep Shift evaluator case matches HOL word_sh oracle"
  else
    IO.println "FAIL crep Shift evaluator case matches HOL word_sh oracle"
  if crepOpEvalGuard then
    IO.println "PASS crep Crepop Mul evaluator case matches HOL crep_op oracle"
  else
    IO.println "FAIL crep Crepop Mul evaluator case matches HOL crep_op oracle"
  if corrGuard then
    IO.println "PASS crep RV64 evaluator correspondence holds on compound expressions"
  else
    IO.println "FAIL crep RV64 evaluator correspondence holds on compound expressions"
  if shiftMatchesGuard then
    IO.println "PASS crep Shift hook matches HOL word_sh over arbitrary model"
  else
    IO.println "FAIL crep Shift hook matches HOL word_sh over arbitrary model"
  if opMatchesGuard then
    IO.println "PASS crep Op hook matches HOL word_op over arbitrary model"
  else
    IO.println "FAIL crep Op hook matches HOL word_op over arbitrary model"
  pure (wordBoundaryGuard && storeRoundTripGuard && loadByteEvalGuard &&
    load32EvalGuard && loadEvalGuard && opEvalGuard && cmpEvalGuard && shiftEvalGuard &&
    crepOpEvalGuard && corrGuard && shiftMatchesGuard && opMatchesGuard)

end Flapjack.Test.CrepRuntimeTargetParity
