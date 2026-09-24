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

/-- Generic `Shift` equation supports arbitrary (nested) child expressions. -/
example :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holShiftBaseState)
        (.shift .lsl (.const 1) (.const 3))).map PanWordLab.word =
      holCrepEval64 holShiftBaseState (.shift .lsl (.const 1) (.const 3)) :=
  evalCrepRuntimeExp_shift_map_eq_holCrepEval64 holShiftBaseState .lsl (.const 1) (.const 3)

/-- The production evaluator over an arbitrary matching model agrees with HOL
    `word_sh` on valid shifts and rejects an out-of-range amount. -/
def shiftMatchesGuard : Bool :=
  (evalCrepRuntimeExp holShiftBaseState (.shift .lsl (.const 1) (.const 3)) ==
      some (8 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holShiftBaseState (.shift .lsl (.const 1) (.const 64)) ==
      none) &&
    (evalCrepRuntimeExp holShiftBaseState (.shift .ror (.const 1) (.const 1)) ==
      some (0x8000000000000000 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holShiftBaseState
        (.shift .lsl (.op .add ([(1 : RiscV.Word 64), 2].map CrepExp.const)) (.const 3)) ==
      some (24 : RiscV.Word 64)) &&
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

/-- Generic `Op` equation supports arbitrary (nested) child expressions. -/
example :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holOpBaseState)
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const))).map PanWordLab.word =
      holCrepEval64 holOpBaseState (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) :=
  evalCrepRuntimeExp_op_map_eq_holCrepEval64 holOpBaseState .add
    ([(3 : RiscV.Word 64), 4].map CrepExp.const)

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
    (evalCrepRuntimeExp holOpBaseState
        (.op .add [.op .sub ([(9 : RiscV.Word 64), 4].map CrepExp.const), .const 4]) ==
      some (9 : RiscV.Word 64)) &&
    (evalCrepRuntimeExpWordLab holOpBaseState
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) ==
      some (.word (7 : RiscV.Word 64))) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holOpBaseState)
        (.op .add ([(3 : RiscV.Word 64), 4].map CrepExp.const)) ==
      some (7 : RiscV.Word 64))

#guard opMatchesGuard
#eval opMatchesGuard

/-- A memory model whose `compare` hook is literally HOL `word_cmp` at 64 bits,
    but which is otherwise not the RISC-V target model. -/
def holCmpModel : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with compare := fun operator left right => evalPanCmp operator left right }

def holCmpBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { probeBaseState with memoryModel := holCmpModel }

theorem holCmpBaseState_matches :
    CrepMemoryModelCmpMatchesHOL64 holCmpBaseState.memoryModel :=
  fun _ _ _ => rfl

example : CrepMemoryModelCmpMatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_cmp_matches_HOL64 corrState

example :
    evalCrepRuntimeExp holCmpBaseState
        (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3)) =
      some (1 : RiscV.Word 64) :=
  evalCrepRuntimeExp_cmp_const_of_matches holCmpBaseState holCmpBaseState_matches .equal 3 3

/-- Generic `Cmp` equation supports arbitrary (nested) child expressions. -/
example :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holCmpBaseState)
        (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3))).map PanWordLab.word =
      holCrepEval64 holCmpBaseState (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3)) :=
  evalCrepRuntimeExp_cmp_map_eq_holCrepEval64 holCmpBaseState .equal (.const 3) (.const 3)

/-- The production evaluator over an arbitrary matching model agrees with HOL
    `word_cmp` on comparisons, including a nested operand. -/
def cmpMatchesGuard : Bool :=
  (evalCrepRuntimeExp holCmpBaseState
      (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3)) ==
    some (1 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holCmpBaseState
        (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 4)) ==
      some (0 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holCmpBaseState
        (.cmp .lower (.const (3 : RiscV.Word 64)) (.const 4)) ==
      some (1 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holCmpBaseState
        (.cmp .test (.const (0 : RiscV.Word 64)) (.const (0xF0 : RiscV.Word 64))) ==
      some (1 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holCmpBaseState
        (.cmp .equal (.op .add ([(1 : RiscV.Word 64), 2].map CrepExp.const)) (.const 3)) ==
      some (1 : RiscV.Word 64)) &&
    (evalCrepRuntimeExpWordLab holCmpBaseState
        (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3)) ==
      some (.word (1 : RiscV.Word 64))) &&
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget holCmpBaseState)
        (.cmp .equal (.const (3 : RiscV.Word 64)) (.const 3)) ==
      some (1 : RiscV.Word 64))

#guard cmpMatchesGuard
#eval cmpMatchesGuard

/-- A memory model whose `byteAlign`/`getByte` hooks are literally the HOL
    functions at 64 bits, but which is otherwise not the RISC-V target model. -/
def holLoadByteModel : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with
    byteAlign := fun _ address => holByteAlign64 address,
    getByte := fun _ address value _ => holGetByte64 address value false }

def holLoadByteBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { loadByteBaseState with memoryModel := holLoadByteModel }

theorem holLoadByteBaseState_matches :
    CrepMemoryModelLoadByteMatchesHOL64 holLoadByteBaseState.memoryModel :=
  fun _ _ => ⟨rfl, rfl⟩

example : CrepMemoryModelLoadByteMatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_loadByte_matches_HOL64 corrState

example :
    evalCrepRuntimeExp holLoadByteBaseState (.loadByte (.const (8 : RiscV.Word 64))) =
      holMemLoadByte64 holLoadByteBaseState.memaddrs
        (crepRuntimeMemoryView holLoadByteBaseState.memory) false 8 :=
  evalCrepRuntimeExp_loadByte_const_of_matches holLoadByteBaseState
    holLoadByteBaseState_matches rfl rfl 8

/-- The production evaluator over an arbitrary matching byte model agrees with
    HOL `mem_load_byte` on constant and recursively evaluated addresses. -/
def loadByteMatchesGuard : Bool :=
  (evalCrepRuntimeExp holLoadByteBaseState
      (.loadByte (.const (8 : RiscV.Word 64))) == some (136 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holLoadByteBaseState
        (.loadByte (.const (9 : RiscV.Word 64))) == some (119 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holLoadByteBaseState
        (.loadByte (.const (16 : RiscV.Word 64))) == none) &&
    (evalCrepRuntimeExpWordLab holLoadByteBaseState
        (.loadByte (.const (8 : RiscV.Word 64))) == some (.word (136 : RiscV.Word 64))) &&
    (evalCrepRuntimeExp holLoadByteBaseState
        (.loadByte (.op .add ([(5 : RiscV.Word 64), 3].map CrepExp.const))) ==
      some (136 : RiscV.Word 64))

#guard loadByteMatchesGuard
#eval loadByteMatchesGuard

/-- A memory model whose alignment, byte-alignment, byte-read, and word-combine
    hooks are literally the HOL `mem_load_32` primitives at 64 bits, but which is
    otherwise not the RISC-V target model. -/
def holLoad32Model : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with
    byteAlign := fun _ address => holByteAlign64 address,
    getByte := fun _ address value _ => holGetByte64 address value false }

def holLoad32BaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { loadByteBaseState with memoryModel := holLoad32Model }

theorem holLoad32BaseState_matches :
    CrepMemoryModelLoad32MatchesHOL64 holLoad32BaseState.memoryModel :=
  fun address _ =>
    ⟨panRiscVAligned32_eq_holAligned32 address, rfl, fun _ => rfl,
      (holWordOfBytes64_eq_panRiscVWordOfBytes false _).symm⟩

example : CrepMemoryModelLoad32MatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_load32_matches_HOL64 corrState

example :
    evalCrepRuntimeExp holLoad32BaseState (.load32 (.const (8 : RiscV.Word 64))) =
      holMemLoad32_64 holLoad32BaseState.memaddrs
        (crepRuntimeMemoryView holLoad32BaseState.memory) false 8 :=
  evalCrepRuntimeExp_load32_const_of_matches holLoad32BaseState
    holLoad32BaseState_matches rfl rfl 8

/-- The production evaluator over an arbitrary matching 32-bit model agrees with
    HOL `mem_load_32` on constant, unaligned, out-of-domain, and nested addresses. -/
def load32MatchesGuard : Bool :=
  (evalCrepRuntimeExp holLoad32BaseState
      (.load32 (.const (8 : RiscV.Word 64))) == some (0x55667788 : RiscV.Word 64)) &&
    (evalCrepRuntimeExp holLoad32BaseState
        (.load32 (.const (9 : RiscV.Word 64))) == none) &&
    (evalCrepRuntimeExp holLoad32BaseState
        (.load32 (.const (16 : RiscV.Word 64))) == none) &&
    (evalCrepRuntimeExpWordLab holLoad32BaseState
        (.load32 (.const (8 : RiscV.Word 64))) ==
      some (.word (0x55667788 : RiscV.Word 64))) &&
    (evalCrepRuntimeExp holLoad32BaseState
        (.load32 (.op .add ([(5 : RiscV.Word 64), 3].map CrepExp.const))) ==
      some (0x55667788 : RiscV.Word 64))

#guard load32MatchesGuard
#eval load32MatchesGuard

/-- A memory model whose byte-alignment and byte-write hooks are literally the
    HOL `set_byte`/in-word primitives at 64 bits, but which is otherwise not the
    RISC-V target model. -/
def holStoreByteModel : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with
    byteAlign := fun _ address => holByteAlign64 address,
    setByte := fun _ address byteValue cell _ => holSetByte64 address byteValue cell false }

def holStoreByteBaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { loadByteBaseState with memoryModel := holStoreByteModel }

theorem holStoreByteBaseState_matches :
    CrepMemoryModelStoreByteMatchesHOL64 holStoreByteBaseState.memoryModel :=
  fun _ _ _ => ⟨rfl, rfl⟩

example :
    CrepMemoryModelStoreByteMatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_storeByte_matches_HOL64 corrState

example :
    crepRuntimeStore holStoreByteBaseState (8 : RiscV.Word 64) 0x77 =
      (holMemStore64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory 8 0x77).map
        (fun memory => { holStoreByteBaseState with memory := memory }) :=
  crepRuntimeStore_eq_holMemStore64 holStoreByteBaseState 8 0x77

example :
    crepRuntimeStoreByte holStoreByteBaseState (8 : RiscV.Word 64) 0x77 =
      (holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 8
        0x77).map (fun memory => { holStoreByteBaseState with memory := memory }) :=
  crepRuntimeStoreByte_eq_holMemStoreByte64_of_matches holStoreByteBaseState
    holStoreByteBaseState_matches rfl rfl 8 0x77

example :
    crepRuntimeStoreByte holStoreByteBaseState (9 : RiscV.Word 64) 0xAA =
      (holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 9
        0xAA).map (fun memory => { holStoreByteBaseState with memory := memory }) :=
  crepRuntimeStoreByte_eq_holMemStoreByte64_of_matches holStoreByteBaseState
    holStoreByteBaseState_matches rfl rfl 9 0xAA

/-- The production word/byte stores over an arbitrary matching model agree with
    HOL `mem_store`/`mem_store_byte`: guarded insertion, byte replacement in the
    aligned cell, and domain failure. -/
def storeByteMatchesGuard : Bool :=
  ((crepRuntimeStore holStoreByteBaseState (8 : RiscV.Word 64) 0x77).map
      (fun state => state.memory 8) == some (.word (0x77 : RiscV.Word 64))) &&
    ((crepRuntimeStoreByte holStoreByteBaseState (8 : RiscV.Word 64) 0x77).map
        (fun state => state.memory 8) == some (.word (0x1122334455667777 : RiscV.Word 64))) &&
    (crepRuntimeStore holStoreByteBaseState (16 : RiscV.Word 64) 0x55).isNone &&
    (crepRuntimeStoreByte holStoreByteBaseState (16 : RiscV.Word 64) 0x55).isNone &&
    ((holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 8
        0x77).map (fun memory => memory 8) ==
      some (.word (0x1122334455667777 : RiscV.Word 64))) &&
    ((crepRuntimeStoreByte holStoreByteBaseState (9 : RiscV.Word 64) 0xAA).map
        (fun state => state.memory 8) ==
      some (.word (0x112233445566AA88 : RiscV.Word 64))) &&
    ((holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 9
        0xAA).map (fun memory => memory 8) ==
      some (.word (0x112233445566AA88 : RiscV.Word 64))) &&
    ((crepRuntimeStoreByte holStoreByteBaseState (9 : RiscV.Word 64) 0xAA).map
        (fun state => state.memory 8) ==
      (holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 9
        0xAA).map (fun memory => memory 8)) &&
    ((crepRuntimeStoreByte holStoreByteBaseState (8 : RiscV.Word 64) 0x77).map
        (fun state => state.memory 8) ==
      (holMemStoreByte64 holStoreByteBaseState.memaddrs holStoreByteBaseState.memory false 8
        0x77).map (fun memory => memory 8))

#guard storeByteMatchesGuard
#eval storeByteMatchesGuard

/-- A non-RISC-V model whose store32 hooks are the HOL `word8`/`set_byte`
    primitives at 64 bits, but which is otherwise not the target model. -/
def holStore32Model : PanMemoryModel (RiscV.Word 64) :=
  { RiscV.panRiscVMemoryModel with
    byteAlign := fun _ address => holByteAlign64 address,
    getByte := fun _ address value _ => holGetByte64 address value false,
    setByte := fun _ address byteValue cell _ => holSetByte64 address byteValue cell false }

def holStore32BaseState : CrepRuntimeState (RiscV.Word 64) Unit :=
  { loadByteBaseState with memoryModel := holStore32Model }

theorem holStore32BaseState_matches :
    CrepMemoryModelStore32MatchesHOL64 holStore32BaseState.memoryModel :=
  fun _ _ _ => ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

example :
    CrepMemoryModelStore32MatchesHOL64 (riscv64CrepRuntimeTarget corrState).memoryModel :=
  riscv64CrepRuntimeTarget_store32_matches_HOL64 corrState

example :
    crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0x11223344 =
      (holMemStore32_64 holStore32BaseState.memaddrs holStore32BaseState.memory false 8
        0x11223344).map (fun memory => { holStore32BaseState with memory := memory }) :=
  crepRuntimeStore32_eq_holMemStore32_64_of_matches holStore32BaseState
    holStore32BaseState_matches rfl rfl 8 0x11223344

example (value : RiscV.Word 64) :
    holGetByte64 0 value false =
      holGetByte64 0 (BitVec.ofNat 64 (value.toNat % 2^32)) false :=
  holGetByte64_low32_eq value 0 (by decide)

example :
    holMemStore32_64 holStore32BaseState.memaddrs holStore32BaseState.memory false 8
        0xDEADBEEF11223344 =
      holMemStore32_64 holStore32BaseState.memaddrs holStore32BaseState.memory false 8
        0x11223344 :=
  holMemStore32_64_high_bits_ignored holStore32BaseState.memaddrs holStore32BaseState.memory
    8 0xDEADBEEF11223344

example :
    crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0xDEADBEEF11223344 =
      crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0x11223344 :=
  crepRuntimeStore32_low32_of_matches holStore32BaseState holStore32BaseState_matches
    rfl rfl 8 0xDEADBEEF11223344

/-- The production 32-bit store over an arbitrary matching model agrees with the
    RV64-lifted counterpart of HOL `mem_store_32`: four-byte replacement in the
    aligned cell, alignment and domain failure.  HOL takes a `word32`; here the
    RV64 value is used through its low 32 bits (`w2w`), so the high bits are
    ignored. -/
def store32MatchesGuard : Bool :=
  ((crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0x11223344).map
      (fun state => state.memory 8) ==
    some (.word (0x1122334411223344 : RiscV.Word 64))) &&
    (crepRuntimeStore32 holStore32BaseState (9 : RiscV.Word 64) 0x11223344).isNone &&
    (crepRuntimeStore32 holStore32BaseState (16 : RiscV.Word 64) 0x11223344).isNone &&
    ((holMemStore32_64 holStore32BaseState.memaddrs holStore32BaseState.memory false 8
        0x11223344).map (fun memory => memory 8) ==
      some (.word (0x1122334411223344 : RiscV.Word 64))) &&
    ((crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0x11223344).map
        (fun state => state.memory 8) ==
      (holMemStore32_64 holStore32BaseState.memaddrs holStore32BaseState.memory false 8
        0x11223344).map (fun memory => memory 8)) &&
    ((crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0xDEADBEEF11223344).map
        (fun state => state.memory 8) ==
      some (.word (0x1122334411223344 : RiscV.Word 64))) &&
    ((crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0xDEADBEEF11223344).map
        (fun state => state.memory 8) ==
      (crepRuntimeStore32 holStore32BaseState (8 : RiscV.Word 64) 0x11223344).map
        (fun state => state.memory 8)) &&
    (holW2w32_64 (0xDEADBEEF11223344 : RiscV.Word 64) == (0x11223344 : BitVec 32))

#guard store32MatchesGuard
#eval store32MatchesGuard

/-! ## Generic program store equations

`evalCrepRuntimeProg_store`, `_store32`, and `_storeByte` expose the production
program store arms of `evalCrepRuntimeProg` over arbitrary operand expressions. -/

def storeProgHandler : CrepRuntimeFfiHandler (RiscV.Word 64) Unit FfiFinalEvent :=
  riscv64SharedMemCallFfiHandler

def storeProgPrimitive : CrepPrimitiveHandler (RiscV.Word 64) := fun _ _ => none

def storeProgStep : Option (CrepRuntimeStep (RiscV.Word 64) Unit FfiFinalEvent) :=
  evalCrepRuntimeProg storeProgHandler storeProgPrimitive 3 holStoreByteBaseState
    (.store (.const (8 : RiscV.Word 64)) (.const (0x77 : RiscV.Word 64)))

def storeProgGuard : Bool :=
  (storeProgStep.map (fun step => step.2.memory 8)) == some (PanWordLab.word 0x77)

#guard storeProgGuard

example : evalCrepRuntimeProg storeProgHandler storeProgPrimitive 4 holStoreByteBaseState
    (.store (.const (8 : RiscV.Word 64)) (.const (0x77 : RiscV.Word 64))) =
      match evalCrepRuntimeExp holStoreByteBaseState (.const (8 : RiscV.Word 64)) with
      | none => some (.error, holStoreByteBaseState)
      | some addressWord =>
          match evalCrepRuntimeExp holStoreByteBaseState (.const (0x77 : RiscV.Word 64)) with
          | none => some (.error, holStoreByteBaseState)
          | some valueWord =>
              match crepRuntimeStore holStoreByteBaseState addressWord valueWord with
              | some state => some (.normal, state)
              | none => some (.error, holStoreByteBaseState) :=
  evalCrepRuntimeProg_store storeProgHandler storeProgPrimitive 3 holStoreByteBaseState
    (.const (8 : RiscV.Word 64)) (.const (0x77 : RiscV.Word 64))

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
    IO.println "PASS crep Shift hook matches HOL word_sh over arbitrary model and nested operands"
  else
    IO.println "FAIL crep Shift hook matches HOL word_sh over arbitrary model and nested operands"
  if opMatchesGuard then
    IO.println "PASS crep Op hook matches HOL word_op over arbitrary model and nested operands"
  else
    IO.println "FAIL crep Op hook matches HOL word_op over arbitrary model and nested operands"
  if cmpMatchesGuard then
    IO.println "PASS crep Cmp hook matches HOL word_cmp over arbitrary model and nested operands"
  else
    IO.println "FAIL crep Cmp hook matches HOL word_cmp over arbitrary model and nested operands"
  if loadByteMatchesGuard then
    IO.println "PASS crep LoadByte hook matches HOL mem_load_byte over arbitrary model and nested operands"
  else
    IO.println "FAIL crep LoadByte hook matches HOL mem_load_byte over arbitrary model and nested operands"
  if load32MatchesGuard then
    IO.println "PASS crep Load32 hook matches HOL mem_load_32 over arbitrary model and nested operands"
  else
    IO.println "FAIL crep Load32 hook matches HOL mem_load_32 over arbitrary model and nested operands"
  if storeByteMatchesGuard then
    IO.println "PASS crep Store/StoreByte hooks match HOL mem_store/mem_store_byte over arbitrary model"
  else
    IO.println "FAIL crep Store/StoreByte hooks match HOL mem_store/mem_store_byte over arbitrary model"
  if store32MatchesGuard then
    IO.println "PASS crep Store32 hook matches HOL mem_store_32 over arbitrary model"
  else
    IO.println "FAIL crep Store32 hook matches HOL mem_store_32 over arbitrary model"
  if storeProgGuard then
    IO.println "PASS crep program store step exposes HOL mem_store over arbitrary operands"
  else
    IO.println "FAIL crep program store step exposes HOL mem_store over arbitrary operands"
  pure (wordBoundaryGuard && storeRoundTripGuard && loadByteEvalGuard &&
    load32EvalGuard && loadEvalGuard && opEvalGuard && cmpEvalGuard && shiftEvalGuard &&
    crepOpEvalGuard && corrGuard && shiftMatchesGuard && opMatchesGuard && cmpMatchesGuard &&
    loadByteMatchesGuard && load32MatchesGuard && storeByteMatchesGuard && store32MatchesGuard &&
    storeProgGuard)

end Flapjack.Test.CrepRuntimeTargetParity
