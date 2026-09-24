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
  pure (wordBoundaryGuard && storeRoundTripGuard && loadByteEvalGuard &&
    load32EvalGuard && loadEvalGuard)

end Flapjack.Test.CrepRuntimeTargetParity
