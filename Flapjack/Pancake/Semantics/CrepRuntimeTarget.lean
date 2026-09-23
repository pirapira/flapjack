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
addresses with `byte$byte_align`. The canonical context below uses the RISC-V helpers that mirror those HOL
functions, so the executable FFI boundary is read as the fixed little-endian
target byte codec. Its `sharedDomain` is the state's shared-memory address
bitmap (`CrepRuntimeState.shMemaddrs`), i.e. HOL `s.sh_memaddrs`, so the
canonical target validates shared-memory addresses with the HOL predicate
(`addr IN s.sh_memaddrs` / `byte_align addr IN s.sh_memaddrs`). Direct oracle:
`scripts/hol-probes/crep_runtime_shared_domain_probe.out`.

The general `wordOfBytes`/`call_FFI` handler relation remains in
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
    HOL `word_to_bytes` produces for the 64-bit target. The shared-memory domain
    is supplied by the caller; the canonical target passes the state's
    `shMemaddrs`, the HOL `s.sh_memaddrs` predicate. -/
def riscv64PanValueFfiContext (sharedDomain : RiscV.Word 64 → Bool) :
    PanValueFfiContext (RiscV.Word 64) where
  sharedDomain := sharedDomain
  byteAlign := RiscV.panRiscVByteAlign (8 : RiscV.Word 64)
  bigEndian := false
  wordToBytes := fun address _ => (List.range 8).map (fun index => riscv64GetByte index address)
  wordOfBytes := fun bigEndian bytes => riscv64PutBytes bigEndian 0 bytes 0
  wordToByte := fun value => riscv64GetByte 0 value
  byteToWord := fun byte => BitVec.ofNat 64 byte.toNat
  valueToNat := fun value => value.toNat

/-- Canonical RISC-V 64 runtime target: fix the target fields that HOL leaves
    fixed by the word type, and read the FFI shared-memory domain from the
    state's shared-memory address bitmap. -/
def riscv64CrepRuntimeTarget (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepRuntimeState (RiscV.Word 64) σ :=
  { base with
    bytesInWord := (8 : RiscV.Word 64)
    bigEndian := false
    memoryModel := RiscV.panRiscVMemoryModel
    ffiContext := riscv64PanValueFfiContext base.shMemaddrs }

/-- Predicate naming the canonical target constraints. -/
def isRiscV64CrepRuntimeTarget (state : CrepRuntimeState (RiscV.Word 64) σ) : Prop :=
  state.bytesInWord = (8 : RiscV.Word 64) ∧
    state.bigEndian = false ∧
    state.memoryModel = RiscV.panRiscVMemoryModel ∧
    state.ffiContext = riscv64PanValueFfiContext state.shMemaddrs

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
    (riscv64CrepRuntimeTarget base).ffiContext =
      riscv64PanValueFfiContext base.shMemaddrs :=
  rfl

/-! ### Shared-memory address validity

HOL `sh_mem_load`/`sh_mem_store` validate an address with `addr IN s.sh_memaddrs`
for width zero and `byte_align addr IN s.sh_memaddrs` for nonzero widths
(`panSemScript.sml:510-524`, `crepSemScript.sml:168-204`). The canonical target
reads `ffiContext.sharedDomain` from the state's shared-memory address bitmap,
so `crepRuntimeSharedAddressValid` is the HOL predicate itself, and a width-zero
op checks the raw address while a width-four op checks the byte-aligned address.
Direct oracle: `scripts/hol-probes/crep_runtime_shared_domain_probe.out`
  valid_zero_mem=T; valid_zero_out=F; valid_aligned_mem=T; valid_aligned_out=F;
  align_9=8w; align_16=16w -/

/-- On the canonical target the FFI shared domain is the state's shared-memory
    address bitmap (HOL `s.sh_memaddrs`). -/
theorem riscv64CrepRuntimeTarget_sharedDomain
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    (riscv64CrepRuntimeTarget base).ffiContext.sharedDomain address =
      (riscv64CrepRuntimeTarget base).shMemaddrs address :=
  rfl

/-- Production `crepRuntimeSharedAddressValid` is the canonical FFI shared
    domain applied to the (byte-aligned) address, i.e. HOL `addr IN
    s.sh_memaddrs` / `byte_align addr IN s.sh_memaddrs`. -/
theorem crepRuntimeSharedAddressValid_eq_sharedDomain
    (base : CrepRuntimeState (RiscV.Word 64) σ) (operator : CrepMemOp)
    (address : RiscV.Word 64) :
    crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base) operator address =
      (riscv64CrepRuntimeTarget base).ffiContext.sharedDomain
        (crepRuntimeSharedAddress (riscv64CrepRuntimeTarget base) operator address) :=
  rfl

/-- Width-zero shared-memory ops validate the raw address, as HOL does when
    `nb = 0`. -/
theorem crepRuntimeSharedAddress_load_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeSharedAddress (riscv64CrepRuntimeTarget base) .load address =
      address :=
  rfl

/-- Width-four shared-memory ops validate the byte-aligned address, as HOL does
    when `nb ≠ 0`; `panRiscVByteAlign 8` is HOL `byte_align` on 64-bit words. -/
theorem crepRuntimeSharedAddress_load32_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeSharedAddress (riscv64CrepRuntimeTarget base) .load32 address =
      RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address :=
  rfl

/-! ### FFI byte-codec bridges

On the canonical target the FFI byte operations are exactly the RISC-V byte
helpers, whose offset arithmetic is HOL `byte$get_byte` / `byte$set_byte` /
`byte$byte_align`. `wordToBytes` is the little-endian byte list handed to the
external handler for `ExtCall` and shared memory, matching HOL `word_to_bytes`.
Direct oracle: `scripts/hol-probes/crep_runtime_ffi_boundary_probe.out`. -/

theorem riscv64PanValueFfiContext_byteAlign_eq_riscv
    (domain : RiscV.Word 64 → Bool) (address : RiscV.Word 64) :
    (riscv64PanValueFfiContext domain).byteAlign address =
      RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address :=
  rfl

theorem riscv64PanValueFfiContext_wordToByte_eq_getByte0
    (domain : RiscV.Word 64 → Bool) (value : RiscV.Word 64) :
    (riscv64PanValueFfiContext domain).wordToByte value = riscv64GetByte 0 value :=
  rfl

theorem riscv64PanValueFfiContext_wordToBytes_eq_getByte
    (domain : RiscV.Word 64 → Bool) (address : RiscV.Word 64) (bigEndian : Bool) :
    (riscv64PanValueFfiContext domain).wordToBytes address bigEndian =
      (List.range 8).map (fun index => riscv64GetByte index address) :=
  rfl

theorem riscv64PanValueFfiContext_valueToNat_eq_riscv
    (domain : RiscV.Word 64 → Bool) (value : RiscV.Word 64) :
    (riscv64PanValueFfiContext domain).valueToNat value = value.toNat :=
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
      RiscV.panRiscVReadWord base.memaddrs (crepRuntimeMemoryView base.memory) address := by
  simp [crepRuntimeLoad, RiscV.panRiscVReadWord, riscv64CrepRuntimeTarget,
    crepRuntimeMemoryView, panTheWord] <;> rfl

theorem crepRuntimeLoadByte_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoadByte (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVReadByte base.memaddrs (crepRuntimeMemoryView base.memory)
        (8 : RiscV.Word 64) address := by
  simp [crepRuntimeLoadByte, RiscV.panRiscVReadByte, panModelReadByte,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel, crepRuntimeMemoryView,
    panTheWord] <;> rfl

theorem crepRuntimeLoad32_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoad32 (riscv64CrepRuntimeTarget base) address =
      RiscV.panRiscVRead32 base.memaddrs (crepRuntimeMemoryView base.memory)
        (8 : RiscV.Word 64) address := by
  simp [crepRuntimeLoad32, RiscV.panRiscVRead32, panModelRead32,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel, crepRuntimeMemoryView,
    panTheWord, BitVec.add_assoc] <;> rfl

/-- `updateMemory` (production, `Flapjack.Semantics`) and
    `panModelUpdateMemory` (the memory-model helper) are definitionally the same
    function, so the store bridges can compare the updated memories directly. -/
theorem updateMemory_eq_panModelUpdateMemory [BEq α] (memory : PanWordMemory α)
    (address value : α) :
    updateMemory memory address value = panModelUpdateMemory memory address value :=
  rfl

theorem updateMemory_eq_updatePanValueMap [BEq α] (memory : PanWordMemory α)
    (address value : α) :
    updateMemory memory address value = updatePanValueMap memory address value :=
  rfl

theorem crepRuntimeStore_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStore (riscv64CrepRuntimeTarget base) address value).map
        (fun state => crepRuntimeMemoryView state.memory) =
      RiscV.panRiscVStoreWord base.memaddrs (crepRuntimeMemoryView base.memory)
        address value := by
  rw [crepRuntimeStore_eq_memory_view]
  simp only [RiscV.panRiscVStoreWord, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]
  by_cases hb : base.memaddrs address = true
  · simp only [hb, if_true]
    rw [updateMemory_eq_updatePanValueMap]
  · simp only [hb, if_false, Bool.false_eq_true]

theorem crepRuntimeStoreByte_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStoreByte (riscv64CrepRuntimeTarget base) address value).map
        (fun state => crepRuntimeMemoryView state.memory) =
      RiscV.panRiscVStoreByte base.memaddrs (crepRuntimeMemoryView base.memory)
        (8 : RiscV.Word 64) address value := by
  rw [crepRuntimeStoreByte_eq_memory_view]
  simp only [RiscV.panRiscVStoreByte, panModelStoreByte, riscv64CrepRuntimeTarget,
    RiscV.panRiscVMemoryModel]
  by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign 8 address) = true
  · simp only [hb, if_true, crepRuntimeMemoryView, Option.pure_def, panTheWord]
    rw [updateMemory_eq_panModelUpdateMemory]
    rfl
  · simp only [hb, if_false, Bool.false_eq_true]

theorem crepRuntimeStore32_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    (crepRuntimeStore32 (riscv64CrepRuntimeTarget base) address value).map
        (fun state => crepRuntimeMemoryView state.memory) =
      RiscV.panRiscVStore32 base.memaddrs (crepRuntimeMemoryView base.memory)
        (8 : RiscV.Word 64) address value := by
  rw [crepRuntimeStore32_eq_memory_view]
  simp only [RiscV.panRiscVStore32, panModelStore32, riscv64CrepRuntimeTarget,
    RiscV.panRiscVMemoryModel, BitVec.add_assoc]
  by_cases ha : RiscV.aligned address 4 = true
  · simp only [ha, if_true]
    by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign 8 address) = true
    · have h1 : (1 + 2 : RiscV.Word 64) = 3 := rfl
      have h2 : (1 + 1 : RiscV.Word 64) = 2 := rfl
      simp only [hb, if_true, crepRuntimeMemoryView, Option.pure_def, panTheWord, h2, h1]
      rw [updateMemory_eq_panModelUpdateMemory]
      rfl
    · simp only [hb, if_false, Bool.false_eq_true]
  · simp only [ha, if_false, Bool.false_eq_true]

/-! ## Evaluator bridges

The production expression evaluator, on the canonical target, uses exactly the
RISC-V memory model operations and the RISC-V word/compare/shift operations.
-/

theorem evalCrepRuntimeExp_load_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVReadWord base.memaddrs (crepRuntimeMemoryView base.memory)) := by
  simp [evalCrepRuntimeExp, crepRuntimeLoad_target_eq_riscv]

theorem evalCrepRuntimeExp_loadByte_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.loadByte address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVReadByte base.memaddrs (crepRuntimeMemoryView base.memory)
          (8 : RiscV.Word 64)) := by
  simp [evalCrepRuntimeExp, crepRuntimeLoadByte_target_eq_riscv]

theorem evalCrepRuntimeExp_load32_target
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load32 address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (RiscV.panRiscVRead32 base.memaddrs (crepRuntimeMemoryView base.memory)
          (8 : RiscV.Word 64)) := by
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

/-! ## External-call byte-array reads

HOL `crepSem$ExtCall` (and `panSem`) read the configuration and array arguments
with `read_bytearray ptr (w2n len) (mem_load_byte s.memory s.memaddrs s.be)`
before handing them to `call_FFI`. `riscv64ReadByteArray` is that read for the
canonical target: `n` bytes from `address`, each the RISC-V byte at that address
(HOL `get_byte` after `byte_align`), low address first. The production
`crepRuntimeReadBytes` is exactly this list; the bridge below is definitional
once the byte load is the RISC-V one.
Direct oracle: `scripts/hol-probes/crep_runtime_read_bytes_probe.out`
  read_bytes_zero=SOME []; read_bytes_short=SOME [1w; 2w; 3w; 4w];
  read_bytes_cross=SOME [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w];
  read_bytes_out_of_domain=NONE -/

/-- HOL `read_bytearray address length (mem_load_byte memory domain false)` for
    the canonical RISC-V 64 target: `length` successive target bytes. -/
def riscv64ReadByteArray (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) : Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
      let value ← RiscV.panRiscVReadByte base.memaddrs (crepRuntimeMemoryView base.memory)
        (8 : RiscV.Word 64) address
      let rest ← riscv64ReadByteArray base (address + 1) length
      pure (riscv64GetByte 0 value :: rest)

/-- Production `crepRuntimeReadBytes` on the canonical target is HOL
    `read_bytearray` with `mem_load_byte`. -/
theorem crepRuntimeReadBytes_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (length : Nat) :
    crepRuntimeReadBytes (riscv64CrepRuntimeTarget base) address length =
      riscv64ReadByteArray base address length := by
  induction length generalizing address with
  | zero => simp [crepRuntimeReadBytes, riscv64ReadByteArray]
  | succ n ih =>
      simp [crepRuntimeReadBytes, riscv64ReadByteArray, ih,
        crepRuntimeLoadByte_target_eq_riscv, riscv64CrepRuntimeTarget_ffiContext,
        riscv64PanValueFfiContext_wordToByte_eq_getByte0]

/-! ## External-call byte-array writes

HOL `crepSem$ExtCall` writes the returned bytes back with
`write_bytearray ptr new_bytes s.memory s.memaddrs s.be`, where
`write_bytearray` is total: when `mem_store_byte` returns `NONE` it keeps the
memory it already had. The production `crepRuntimeWriteBytes` mirrors this by
keeping the tail state on a `NONE` store. `riscv64SetMemory`/`riscv64WriteMem`
are the canonical target witness of that write.
Direct oracle: `scripts/hol-probes/crep_runtime_write_bytes_probe.out`. -/

/-- Put a total memory into a canonical target state, keeping every other field. -/
def riscv64SetMemory (base : CrepRuntimeState (RiscV.Word 64) σ)
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64)) :
    CrepRuntimeState (RiscV.Word 64) σ :=
  { riscv64CrepRuntimeTarget base with memory := memory }

/-- Putting the state's own memory back is the canonical target itself. -/
theorem riscv64SetMemory_self (base : CrepRuntimeState (RiscV.Word 64) σ) :
    riscv64SetMemory base base.memory = riscv64CrepRuntimeTarget base := rfl

/-- The production byte writer's step: store (with HOL's total fallback) at the
    head address after writing the tail. -/
theorem crepRuntimeWriteBytes_cons (s : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (byte : UInt8) (bytes : List UInt8) :
    crepRuntimeWriteBytes s address (byte :: bytes) =
      (crepRuntimeWriteBytes s (address + 1) bytes).map
        (fun tailState =>
          (crepRuntimeStoreByte tailState address (s.ffiContext.byteToWord byte)).getD
            tailState) := by
  rw [crepRuntimeWriteBytes]
  cases hrec : crepRuntimeWriteBytes s (address + 1) bytes with
  | none => rfl
  | some tailState =>
      simp [Option.getD]
      cases crepRuntimeStoreByte tailState address (s.ffiContext.byteToWord byte) <;> rfl

/-- HOL `write_bytearray address bytes memory domain false` for the canonical
    RISC-V 64 target: writes the bytes tail-first (matching HOL), keeping the
    previous state whenever a byte store fails. -/
def riscv64WriteState (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) : List UInt8 → CrepRuntimeState (RiscV.Word 64) σ
  | [] => riscv64CrepRuntimeTarget base
  | byte :: bytes =>
      (crepRuntimeStoreByte (riscv64WriteState base (address + 1) bytes) address
        ((riscv64CrepRuntimeTarget base).ffiContext.byteToWord byte)).getD
        (riscv64WriteState base (address + 1) bytes)

/-- The memory produced by `riscv64WriteState`, i.e. the HOL `write_bytearray`
    result for `mem_store_byte`. -/
def riscv64WriteMem (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (bytes : List UInt8) :
    RiscV.Word 64 → PanWordLab (RiscV.Word 64) :=
  (riscv64WriteState base address bytes).memory

/-- Production `crepRuntimeWriteBytes` on the canonical target is the total HOL
    `write_bytearray` for `mem_store_byte`. -/
theorem crepRuntimeWriteBytes_target_eq_riscv_state
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (bytes : List UInt8) :
    crepRuntimeWriteBytes (riscv64CrepRuntimeTarget base) address bytes =
      some (riscv64WriteState base address bytes) := by
  induction bytes generalizing address with
  | nil => simp [crepRuntimeWriteBytes, riscv64WriteState]
  | cons byte bytes ih =>
      rw [crepRuntimeWriteBytes_cons, ih (address + 1), Option.map_some]
      rfl

/-- Memory-level form of the write-bytes bridge (the produced memory is exactly
    the HOL `write_bytearray` result). -/
theorem crepRuntimeWriteBytes_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (bytes : List UInt8) :
    (crepRuntimeWriteBytes (riscv64CrepRuntimeTarget base) address bytes).map
        (fun state => state.memory) =
      some (riscv64WriteMem base address bytes) := by
  rw [crepRuntimeWriteBytes_target_eq_riscv_state]
  rfl

/-! ## External-call dispatch

HOL `crepSem$ExtCall` reads the configuration and array arguments from memory
with `read_bytearray ptr (w2n len) (mem_load_byte s.memory s.memaddrs s.be)`,
then calls `call_FFI s.ffi (ExtCall ffi_index) configuration array`. On
`FFI_return` it writes the returned bytes back with `write_bytearray` and
updates the ffi state; on `FFI_final` it returns `FinalFFI` with the state
unchanged; if either argument read fails it returns `Error`.

The production `crepRuntimeExtCallValues` is related below to the Lean port
`callFfi` (the counterpart of `call_FFI`), and the argument reads are the
already-bridged `read_bytearray`. The handler payload codec
(`wordOfBytes`/`valueToNat`) and the four-local `crepRuntimeExtCall` wrapper
remain tracked in `flapjack-pxn.18.4.3.43.1.2.2`.
Direct oracle: `scripts/hol-probes/crep_runtime_ext_call_probe.out`. -/

/-- The canonical external-call handler for the RISC-V 64 target: it is the
    Lean `callFfi` (the `call_FFI` port) lifted into the `CrepRuntimeFfiHandler`
    response shape. The `sharedMem` case is dead for the `ExtCall` relation and
    just returns the unchanged ffi with no bytes. -/
def riscv64ExtCallCallFfiHandler :
    CrepRuntimeFfiHandler α σ FfiFinalEvent
  | .extCall function configuration array, ffi =>
      match callFfi ffi (.extCall function) configuration array with
      | .returned nextFfi bytes => .returned nextFfi bytes
      | .final event => .final event
  | .sharedMem _ _ _ _, ffi => .returned ffi []

/-- `riscv64CrepRuntimeTarget` does not inspect the ffi state, so lifting it over
    an ffi update commutes with the record update. -/
theorem riscv64CrepRuntimeTarget_withFfi
    (base : CrepRuntimeState (RiscV.Word 64) σ) (ffi : FfiState σ) :
    riscv64CrepRuntimeTarget { base with ffi := ffi } =
      { riscv64CrepRuntimeTarget base with ffi := ffi } := rfl

/-- The canonical target keeps the caller's ffi state. -/
theorem riscv64CrepRuntimeTarget_ffi
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    (riscv64CrepRuntimeTarget base).ffi = base.ffi := rfl

/-- Write-bytes bridge for an ffi-updated canonical target: the production writer
    is the canonical RISC-V `write_bytearray` and installs the given ffi. -/
theorem crepRuntimeWriteBytes_target_updateFfi
    (base : CrepRuntimeState (RiscV.Word 64) σ) (ffi : FfiState σ)
    (address : RiscV.Word 64) (bytes : List UInt8) :
    crepRuntimeWriteBytes { riscv64CrepRuntimeTarget base with ffi := ffi }
        address bytes =
      some (riscv64WriteState { base with ffi := ffi } address bytes) := by
  dsimp only
  rw [← riscv64CrepRuntimeTarget_withFfi base ffi,
    crepRuntimeWriteBytes_target_eq_riscv_state]

/-- The canonical-target `ExtCall` handler lifts HOL `call_FFI` to the Crep
    runtime request/response boundary: an `extCall` request dispatches to
    `callFfi` (the Lean counterpart of HOL `ffi$call_FFI`) and maps its
    `FfiResult` to the Crep handler response.  Direct oracle:
    `scripts/hol-probes/crep_runtime_ext_call_probe.out`. -/
theorem riscv64ExtCallCallFfiHandler_extCall
    (function : FunName) (configuration array : List UInt8) (ffi : FfiState σ) :
    riscv64ExtCallCallFfiHandler
        (.extCall function configuration array :
          CrepRuntimeRequest (RiscV.Word 64)) ffi =
      (match callFfi ffi (.extCall function) configuration array with
       | .returned nextFfi bytes => .returned nextFfi bytes
       | .final event => .final event) := rfl

/-- The `ExtCall` handler leaves a `sharedMem` request untouched, returning the
    ffi unchanged.  Direct oracle follows from the same HOL `call_FFI` case
    analysis; included so the handler is characterised on every request. -/
theorem riscv64ExtCallCallFfiHandler_sharedMem
    (operator : CrepMemOp) (name : Nat) (address : RiscV.Word 64)
    (payload : List UInt8) (ffi : FfiState σ) :
    riscv64ExtCallCallFfiHandler
        (.sharedMem operator name address payload) ffi = .returned ffi [] := rfl

/-- Canonical-target dispatch of `crepRuntimeExtCallValues`.  The two HOL
    `ExtCall` non-returning outcomes are pinned here: a failed configuration or
    array read returns `Error` (HOL's `_ => (SOME Error, s)`), and an ffi `final`
    event returns `FinalFFI` with the target state unchanged (HOL `FFI_final`).
    The `returned` branch (HOL `FFI_return`: write the returned bytes back with
    the canonical target writer and install the returned ffi) is the remaining
    gap, tracked in child bead `flapjack-pxn.18.4.3.43.1.2.2.1.1`; separately
    elaborated occurrences of the well-founded `crepRuntimeWriteBytes` do not
    share their hidden instance arguments, so that equalities is not `rfl`. -/
theorem crepRuntimeExtCallValues_target_error
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (h : riscv64ReadByteArray base configuration configurationLength.toNat = none ∨
         riscv64ReadByteArray base array arrayLength.toNat = none) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.error, riscv64CrepRuntimeTarget base) := by
  unfold crepRuntimeExtCallValues
  simp only [riscv64CrepRuntimeTarget_ffiContext,
    riscv64PanValueFfiContext_valueToNat_eq_riscv,
    crepRuntimeReadBytes_target_eq_riscv]
  rcases h with h | h <;> simp [h]

/-- Dispatch when the `callFfi` handler reports a `final` event (HOL
    `FFI_final`): the production step returns `FinalFFI` with the target state
    unchanged, exactly HOL's `call_FFI` final branch.  The `returned` branch
    (write-back) is tracked in child bead `flapjack-pxn.18.4.3.43.1.2.2.1.1`. -/
theorem crepRuntimeExtCallValues_target_final
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8)
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (event : FfiFinalEvent)
    (hf : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .final event) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.finalFfi event, riscv64CrepRuntimeTarget base) := by
  unfold crepRuntimeExtCallValues
  simp only [riscv64CrepRuntimeTarget_ffiContext,
    riscv64PanValueFfiContext_valueToNat_eq_riscv,
    crepRuntimeReadBytes_target_eq_riscv, riscv64CrepRuntimeTarget_ffi, hc, ha, hf]

/-! Dispatch when the `callFfi` handler reports a `returned` result (HOL
    `FFI_return`): the production step writes the returned bytes back into the
    array argument with the canonical target writer and installs the returned
    ffi, exactly HOL's `FFI_return` branch (`write_bytearray` + `ffi:=new_ffi`).
    This last `ExtCall` outcome remains open in child bead
    `flapjack-pxn.18.4.3.43.1.2.2.1.1`: the production occurrence of
    `crepRuntimeWriteBytes` inside `crepRuntimeExtCallValues` is elaborated with
    a `let`/projection form of the updated state that does not syntactically
    match the `{ .. with ffi := .. }` form of the proven
    `crepRuntimeWriteBytes_target_updateFfi` bridge, and `rw`/`simp`/`change`/
    `convert` keyed matching does not close the gap.  The write-back relation
    itself is proven (`crepRuntimeWriteBytes_target_eq_riscv_state`); only its
    composition into the one-shot dispatch expression is blocked. -/

end Flapjack
