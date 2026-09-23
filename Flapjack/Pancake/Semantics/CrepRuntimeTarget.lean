import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.RiscV.PanMemory

/-!
# Canonical RISC-V 64 target for the Crep runtime

`CrepRuntimeState` leaves `bytesInWord`, `memoryModel`, and `bigEndian`
unconstrained. HOL `panSem$state` instead fixes `bytes_in_word` by the word type
(`byte$bytes_in_word = n2w (dimindex (:'a) DIV 8)`) and fixes `mem_load_byte` /
`mem_load_32` accordingly (panSemScript.sml:86-106), while `crepSem$state` has no
such fields at all.

This module gives the production `CrepRuntimeState` operations a canonical
RISC-V 64 instance and proves that, on that instance, they are exactly the
RISC-V pan memory model operations. These are production statements about
`crepRuntimeLoad`/`crepRuntimeLoad32`/`crepRuntimeLoadByte`,
`crepRuntimeStore`/`crepRuntimeStoreByte`, and `evalCrepRuntimeExp`, so the
executable evaluator can be read as a fixed target rather than an arbitrary
model. Nothing here changes a tagged declaration or adds a premise to one; the
target is an ordinary predicate/instance, and `stateRel` is untouched.

The whole production store/load boundary is covered: the 32-bit variants use
the `BitVec` numeral normalizations `a + 1 + 1 = a + 2`,
`a + 1 + 1 + 1 = a + 3`, and `1 + 1 + 1 = 3`; the four-step `setByte` chain of
`crepRuntimeStore32` then matches `panModelStore32` exactly. Nothing here
changes a tagged declaration or adds a premise to one; the target is an
ordinary predicate/instance, and `stateRel` is untouched.

Direct HOL oracle: `scripts/hol-probes/crep_runtime_word_boundary_probe.out`
  bytes64=8w; bytes32=4w; byte_at_9=SOME 2w; byte_at_8=SOME 1w;
  byte_outside_domain=NONE; word32_at_8=SOME 0x4030201w;
  word32_unaligned=NONE; store_byte_roundtrip=SOME 0xABw;
  store_byte_outside=NONE; store32_roundtrip=SOME 0xAABBCCDDw;
  store32_unaligned=NONE; store32_outside=NONE

`ffiContext` is fixed to the canonical RISC-V 64 byte codec
(`riscv64PanValueFfiContext`), so the executable external-call/shared-memory
byte boundary uses the same `get_byte`/`set_byte`/`byte_align` arithmetic as HOL.
Direct HOL oracle: `scripts/hol-probes/crep_runtime_ffi_boundary_probe.out`
  bytes64=8w; get_byte_0=8w; get_byte_1=7w; get_byte_7=1w; byte_align_8=8w;
  byte_align_16=16w; word_to_bytes_64=[8w; 7w; 6w; 5w; 4w; 3w; 2w; 1w];
  word_of_bytes_roundtrip=0x102030405060708w; set_byte_0_roundtrip=0x102030405060708w
-/

namespace Flapjack

/-! ## Canonical FFI byte codec

`CrepRuntimeState.ffiContext` is unconstrained, yet `crepRuntimeReadBytes`,
`crepRuntimeWriteBytes`, `crepRuntimeExtCallValues`, and `crepRuntimeSharedMem`
all take the byte representation of a machine word from it before handing bytes
to the external handler. HOL's `call_FFI` receives that byte list as produced by
`byte$word_to_bytes` / `byte$get_byte`, while `crepSem` validates shared-memory
addresses with `byte$byte_align`. The canonical RISC-V 64 context below uses the
RISC-V helpers that mirror those HOL functions, so the executable FFI boundary
is read as the fixed little-endian target byte codec.

The `sharedDomain` field is deliberately total here; constraining shared-memory
address validity is tracked in child bead `flapjack-pxn.18.4.3.43.1.1`, and the
general `wordOfBytes`/`call_FFI` handler relation in
`flapjack-pxn.18.4.3.43.1.2`. -/

/-- The RISC-V byte at `index` of `value`, reusing the pan memory model's
    `panRiscVGetByte` (the same offset arithmetic as HOL `byte$get_byte`). -/
def riscv64GetByte (index : Nat) (value : RiscV.Word 64) : UInt8 :=
  UInt8.ofNat
    (RiscV.panRiscVGetByte (8 : RiscV.Word 64) (BitVec.ofNat 64 index) value).toNat

/-- Insert bytes at increasing addresses, mirroring HOL `byte$word_of_bytes`
    (which starts at address `a` and increments by one word per byte). -/
def riscv64PutBytes (bigEndian : Bool) : Nat → List UInt8 → RiscV.Word 64 → RiscV.Word 64
  | _, [], value => value
  | index, byte :: bytes, value =>
      riscv64PutBytes bigEndian (index + 1) bytes
        (RiscV.panRiscVSetByte (8 : RiscV.Word 64) (BitVec.ofNat 64 index)
          (BitVec.ofNat 64 byte.toNat) value)

/-- Canonical RISC-V 64 FFI byte codec: little-endian bytes, low byte first, as
    HOL `word_to_bytes` produces for the 64-bit target. -/
def riscv64PanValueFfiContext : PanValueFfiContext (RiscV.Word 64) where
  sharedDomain := fun _ => true
  byteAlign := RiscV.panRiscVByteAlign (8 : RiscV.Word 64)
  bigEndian := false
  wordToBytes := fun address _ => (List.range 8).map (fun index => riscv64GetByte index address)
  wordOfBytes := fun bigEndian bytes => riscv64PutBytes bigEndian 0 bytes 0
  wordToByte := fun value => riscv64GetByte 0 value
  byteToWord := fun byte => BitVec.ofNat 64 byte.toNat
  valueToNat := fun value => value.toNat

/-- Canonical RISC-V 64 runtime target: fix the three target fields that HOL
    leaves fixed by the word type. -/
def riscv64CrepRuntimeTarget (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepRuntimeState (RiscV.Word 64) σ :=
  { base with
    bytesInWord := (8 : RiscV.Word 64)
    bigEndian := false
    memoryModel := RiscV.panRiscVMemoryModel
    ffiContext := riscv64PanValueFfiContext }

/-- Predicate naming the canonical target constraints. -/
def isRiscV64CrepRuntimeTarget (state : CrepRuntimeState (RiscV.Word 64) σ) : Prop :=
  state.bytesInWord = (8 : RiscV.Word 64) ∧
    state.bigEndian = false ∧
    state.memoryModel = RiscV.panRiscVMemoryModel ∧
    state.ffiContext = riscv64PanValueFfiContext

theorem riscv64CrepRuntimeTarget_isTarget
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    isRiscV64CrepRuntimeTarget (riscv64CrepRuntimeTarget base) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The canonical target fixes `bytesInWord` to the word-type value used by HOL
    `byte$bytes_in_word` (64 DIV 8 = 8). -/
theorem riscv64CrepRuntimeTarget_bytesInWord
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).bytesInWord = CrepBytesInWord.bytesInWord :=
  rfl

theorem riscv64CrepRuntimeTarget_bigEndian
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).bigEndian = false :=
  rfl

theorem riscv64CrepRuntimeTarget_memoryModel
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).memoryModel = RiscV.panRiscVMemoryModel :=
  rfl

theorem riscv64CrepRuntimeTarget_ffiContext
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).ffiContext = riscv64PanValueFfiContext :=
  rfl

/-! ### FFI byte-codec bridges

On the canonical target the FFI byte operations are exactly the RISC-V byte
helpers, whose offset arithmetic is HOL `byte$get_byte` / `byte$set_byte` /
`byte$byte_align`. `wordToBytes` is the little-endian byte list handed to the
external handler for `ExtCall` and shared memory, matching HOL `word_to_bytes`.
Direct oracle: `scripts/hol-probes/crep_runtime_ffi_boundary_probe.out`. -/

theorem riscv64PanValueFfiContext_byteAlign_eq_riscv (address : RiscV.Word 64) :
    riscv64PanValueFfiContext.byteAlign address =
      RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address :=
  rfl

theorem riscv64PanValueFfiContext_wordToByte_eq_getByte0 (value : RiscV.Word 64) :
    riscv64PanValueFfiContext.wordToByte value = riscv64GetByte 0 value :=
  rfl

theorem riscv64PanValueFfiContext_wordToBytes_eq_getByte
    (address : RiscV.Word 64) (bigEndian : Bool) :
    riscv64PanValueFfiContext.wordToBytes address bigEndian =
      (List.range 8).map (fun index => riscv64GetByte index address) :=
  rfl

theorem riscv64PanValueFfiContext_valueToNat_eq_riscv (value : RiscV.Word 64) :
    riscv64PanValueFfiContext.valueToNat value = value.toNat :=
  rfl

theorem riscv64CrepRuntimeTarget_idem
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    riscv64CrepRuntimeTarget (riscv64CrepRuntimeTarget base) =
      riscv64CrepRuntimeTarget base :=
  rfl

/-! ## Memory-operation bridges

On the canonical target, each production runtime memory operation is the
corresponding RISC-V pan memory model operation. The plain load/store agree
definitionally; the 32-bit variants only need the `BitVec` numeral
normalization `a + 1 + 1 = a + 2` and `a + 1 + 1 + 1 = a + 3`.
-/

theorem crepRuntimeLoad_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoad (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVReadWord base.memaddrs base.memory address := by
  simp [crepRuntimeLoad, RiscV.panRiscVReadWord, riscv64CrepRuntimeTarget ] <;> rfl

theorem crepRuntimeLoadByte_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoadByte (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVReadByte base.memaddrs base.memory (8 : RiscV.Word 64) address := by
  simp [crepRuntimeLoadByte, RiscV.panRiscVReadByte, panModelReadByte,
    riscv64CrepRuntimeTarget , RiscV.panRiscVMemoryModel] <;> rfl

theorem crepRuntimeLoad32_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoad32 (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVRead32 base.memaddrs base.memory (8 : RiscV.Word 64) address := by
  simp [crepRuntimeLoad32, RiscV.panRiscVRead32, panModelRead32,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel, BitVec.add_assoc ] <;> rfl

theorem crepRuntimeStore_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStore (riscv64CrepRuntimeTarget base) address value).map
        (fun state => state.memory) =
      RiscV.panRiscVStoreWord base.memaddrs base.memory address value := by
  rw [crepRuntimeStore, RiscV.panRiscVStoreWord, riscv64CrepRuntimeTarget]
  by_cases hb : base.memaddrs address = true
  · rw [if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb]
    rfl

theorem crepRuntimeStoreByte_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStoreByte (riscv64CrepRuntimeTarget base) address value).map
        (fun state => state.memory) =
      RiscV.panRiscVStoreByte base.memaddrs base.memory (8 : RiscV.Word 64)
        address value := by
  rw [crepRuntimeStoreByte, RiscV.panRiscVStoreByte, panModelStoreByte,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]
  by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign 8 address) = true
  · rw [if_pos hb, if_pos hb]
    cases hm : base.memory (RiscV.panRiscVByteAlign 8 address) <;> rfl
  · rw [if_neg hb, if_neg hb]
    rfl

/-- `updateMemory` (production, `Flapjack.Semantics`) and
    `panModelUpdateMemory` (the memory-model helper) are definitionally the same
    function, so the store bridges can compare the updated memories directly. -/
theorem updateMemory_eq_panModelUpdateMemory [BEq α] (memory : PanWordMemory α)
    (address value : α) :
    updateMemory memory address value = panModelUpdateMemory memory address value :=
  rfl

theorem crepRuntimeStore32_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStore32 (riscv64CrepRuntimeTarget base) address value).map
        (fun state => state.memory) =
      RiscV.panRiscVStore32 base.memaddrs base.memory (8 : RiscV.Word 64)
        address value := by
  rw [crepRuntimeStore32, RiscV.panRiscVStore32, panModelStore32,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]
  by_cases ha : RiscV.aligned address 4 = true
  · rw [if_pos ha, if_pos ha]
    by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign 8 address) = true
    · rw [if_pos hb, if_pos hb]
      cases hm : base.memory (RiscV.panRiscVByteAlign 8 address) <;>
        simp [updateMemory_eq_panModelUpdateMemory, BitVec.add_assoc]
    · rw [if_neg hb, if_neg hb]
      rfl
  · rw [if_neg ha, if_neg ha]
    rfl

/-! ## Evaluator bridges

The production expression evaluator, on the canonical target, uses exactly the
RISC-V memory model operations and the RISC-V word/compare/shift operations.
-/

theorem evalCrepRuntimeExp_load_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVReadWord base.memaddrs base.memory) := by
  simp [evalCrepRuntimeExp, crepRuntimeLoad_target_eq_riscv]

theorem evalCrepRuntimeExp_loadByte_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.loadByte address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVReadByte base.memaddrs base.memory (8 : RiscV.Word 64)) := by
  simp [evalCrepRuntimeExp, crepRuntimeLoadByte_target_eq_riscv]

theorem evalCrepRuntimeExp_load32_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load32 address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVRead32 base.memaddrs base.memory (8 : RiscV.Word 64)) := by
  simp [evalCrepRuntimeExp, crepRuntimeLoad32_target_eq_riscv]

theorem evalCrepRuntimeExp_op_target
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word 64))) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.op operator expressions) =
      (expressions.mapM (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base))).bind
        (RiscV.panRiscVWordOp operator) := by
  simp [evalCrepRuntimeExp, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]

theorem evalCrepRuntimeExp_cmp_target
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Cmp) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.cmp operator left right) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) left).bind
        (fun leftValue =>
          (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) right).bind
            (fun rightValue => some (RiscV.panRiscVCmp operator leftValue rightValue))) := by
  simp [evalCrepRuntimeExp, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]

theorem evalCrepRuntimeExp_shift_target
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Shift) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.shift operator left right) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) left).bind
        (fun leftValue =>
          (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) right).bind
            (RiscV.panRiscVShift operator leftValue)) := by
  simp [evalCrepRuntimeExp, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]

end Flapjack
