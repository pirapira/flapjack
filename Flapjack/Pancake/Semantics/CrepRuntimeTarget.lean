import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.WordLang
import Flapjack.PanSemWriteBytearray
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

/-! The expression evaluator needs the word cell operations that HOL derives
    from the word width. This target fixes those operations for any positive
    BitVec width and preserves HOL's state endianness for byte loads; unlike
    `riscv64CrepRuntimeTarget`, its FFI fields are left untouched because
    expression evaluation never reads them. -/
def riscvCrepWordTarget [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) :
    CrepRuntimeState (RiscV.Word width) σ :=
  { base with
    bytesInWord := BitVec.ofNat width (width / 8)
    bigEndian := base.bigEndian
    memoryModel := RiscV.panRiscVMemoryModelForEndian base.bigEndian }

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

/-! The expression theorem is width-polymorphic, so its target boundary needs
word-operation and byte-load equations for every positive word width, not only
the executable 64-bit image. These equations retain arbitrary source memory
and address-domain fields. -/

theorem crepRuntimeLoad_wordTarget_eq_riscv [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoad (riscvCrepWordTarget base) address =
      RiscV.panRiscVReadWord base.memaddrs (crepRuntimeMemoryView base.memory) address := by
  simp [crepRuntimeLoad, RiscV.panRiscVReadWord, riscvCrepWordTarget,
    crepRuntimeMemoryView, panTheWord] <;> rfl

theorem crepRuntimeLoadByte_wordTarget_eq_riscv [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoadByte (riscvCrepWordTarget base) address =
      panModelReadByte (RiscV.panRiscVMemoryModelForEndian base.bigEndian)
        base.memaddrs (crepRuntimeMemoryView base.memory)
        (BitVec.ofNat width (width / 8)) address base.bigEndian := by
  simp [crepRuntimeLoadByte, panModelReadByte, riscvCrepWordTarget,
    RiscV.panRiscVMemoryModelForEndian, crepRuntimeMemoryView, panTheWord] <;> rfl

theorem crepRuntimeLoad32_wordTarget_eq_riscv [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (address : RiscV.Word width) :
    crepRuntimeLoad32 (riscvCrepWordTarget base) address =
      panModelRead32 (RiscV.panRiscVMemoryModelForEndian base.bigEndian)
        base.memaddrs (crepRuntimeMemoryView base.memory)
        (BitVec.ofNat width (width / 8)) address base.bigEndian := by
  have haddr2 : address + 1 + 1 = address + 2 := by
    calc
      (address + 1) + 1 = address + (1 + 1) := BitVec.add_assoc _ _ _
      _ = address + 2 := by
        congr 1
        change BitVec.ofNat width 1 + BitVec.ofNat width 1 = BitVec.ofNat width 2
        rw [BitVec.ofNat_add_ofNat]
  have h23 : (2 : RiscV.Word width) + 1 = 3 := by
    change BitVec.ofNat width 2 + BitVec.ofNat width 1 = BitVec.ofNat width 3
    rw [BitVec.ofNat_add_ofNat]
  have haddr32 : address + 2 + 1 = address + 3 := by
    calc
      (address + 2) + 1 = address + (2 + 1) := BitVec.add_assoc _ _ _
      _ = address + 3 := by rw [h23]
  unfold crepRuntimeLoad32
  simp only [riscvCrepWordTarget, panModelRead32, crepRuntimeMemoryView,
    panTheWord, RiscV.panRiscVMemoryModelForEndian]
  simp only [haddr2, haddr32]
  rfl

theorem crepRuntimeWordTarget_wordOp [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (operator : BinOp)
    (values : List (RiscV.Word width)) :
    (riscvCrepWordTarget base).memoryModel.wordOp operator values =
      RiscV.panRiscVWordOp operator values := rfl

/-! The RISC-V production model's list-valued operation is the HOL
`word_op_def` port at every positive BitVec width. This closes the
operation-field step for expression evaluation; it does not by itself identify
the target-extended runtime state with a HOL `crepSem$state`. -/
theorem panRiscVWordOp_eq_wordOpHOL [NeZero width]
    (operator : BinOp) (values : List (RiscV.Word width)) :
    RiscV.panRiscVWordOp operator values = wordOpHOL operator values := rfl

/-! The production `Op` constructor evaluates the full expression list and
then applies the width-generic HOL `word_op_def` port. This is an evaluator
constructor bridge for the canonical RISC-V word target, not the whole HOL
`crepSem$eval` relation: the runtime state and other evaluator constructors
still require their own correspondence proofs. -/
theorem evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word width))) :
    evalCrepRuntimeExp (riscvCrepWordTarget base) (.op operator expressions) =
      (expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget base))).bind
        (wordOpHOL operator) := by
  simp only [evalCrepRuntimeExp, riscvCrepWordTarget,
    RiscV.panRiscVMemoryModelForEndian]
  change (expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget base))).bind
      (fun values => RiscV.panRiscVWordOp operator values) =
    (expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget base))).bind
      (wordOpHOL operator)
  apply congrArg
    (fun operation =>
      (expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget base))).bind operation)
  funext values
  exact panRiscVWordOp_eq_wordOpHOL operator values

/-- The same all-width `Op` constructor equation with HOL's complete
`Option (word_lab word)` result projection. This is still only one evaluator
case for the target-adapted runtime, not a claim that its entire state is a
HOL `crepSem$state`. -/
theorem evalCrepRuntimeExp_op_riscvWordTarget_wordLab [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word width))) :
    (evalCrepRuntimeExp (riscvCrepWordTarget base) (.op operator expressions)).map
        PanWordLab.word =
      (expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget base))).bind
        (fun values => (wordOpHOL operator values).map PanWordLab.word) := by
  rw [evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
  simp [Option.map_bind, Function.comp_def]

theorem crepRuntimeWordTarget_compare [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (operator : Cmp)
    (left right : RiscV.Word width) :
    (riscvCrepWordTarget base).memoryModel.compare operator left right =
      RiscV.panRiscVCmp operator left right := rfl

theorem crepRuntimeWordTarget_shift [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ) (operator : Shift)
    (left right : RiscV.Word width) :
    (riscvCrepWordTarget base).memoryModel.shift operator left right =
      RiscV.panRiscVShift operator left right := rfl

/-! `evalPanShiftFull` is the width-parametric Lean counterpart of HOL's
`word_sh_def`. The canonical production target uses `panRiscVShift`; this
lemma proves those two interfaces agree for every positive word width. -/
theorem panRiscVShift_eq_evalPanShiftFull [NeZero width]
    (operator : Shift) (left right : RiscV.Word width) :
    RiscV.panRiscVShift operator left right = evalPanShiftFull operator left right := by
  change RiscV.panRiscVShift operator left right =
    (if right.toNat ≠ 0 ∧ width ≤ right.toNat then none else
      match operator with
      | .lsl => some (left <<< right.toNat)
      | .lsr => some (left >>> right.toNat)
      | .asr => some (BitVec.sshiftRight left right.toNat)
      | .ror => some (BitVec.rotateRight left right.toNat))
  by_cases hlt : right.toNat < width
  · have hnot : ¬ (right.toNat ≠ 0 ∧ width ≤ right.toNat) := by omega
    simp [RiscV.panRiscVShift, hlt, hnot] <;> rfl
  · have hle : width ≤ right.toNat := Nat.le_of_not_gt hlt
    have hpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    have hnz : right.toNat ≠ 0 := by
      intro hz
      omega
    simp [RiscV.panRiscVShift, hlt, hle, hnz]

theorem panRiscVCmp_eq_evalPanCmp [NeZero width]
    (operator : Cmp) (left right : RiscV.Word width) :
    RiscV.panRiscVCmp operator left right = evalPanCmp operator left right := by
  cases operator with
  | equal => simp [RiscV.panRiscVCmp, evalPanCmp] <;> split <;> rfl
  | notEqual => simp [RiscV.panRiscVCmp, evalPanCmp] <;> split <;> rfl
  | lower =>
      simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_lower] <;> split <;> rfl
  | notLower =>
      by_cases h : left < right
      · simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_lower, h]
      · simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_lower, h]
  | less =>
      simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_less] <;> split <;> rfl
  | notLess =>
      by_cases h : RiscV.signedLess left right
      · simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_less, h]
      · simp [RiscV.panRiscVCmp, evalPanCmp, RiscV.panCmp_word_less, h]
  | test => simp [RiscV.panRiscVCmp, evalPanCmp] <;> split <;> rfl
  | notTest => simp [RiscV.panRiscVCmp, evalPanCmp] <;> split <;> rfl

/-! These constructor equations expose the production target's generic
    comparison and shift primitives through the evaluator's recursive child
    evaluations. They remain untagged support: the target-adapted state is not
    yet identified with arbitrary HOL `crepSem$state`. -/
private theorem evalCrepRuntimeExp_cmp_raw
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : Cmp)
    (left right : CrepExp α) :
    evalCrepRuntimeExp state (.cmp operator left right) =
      (evalCrepRuntimeExp state left).bind (fun leftValue =>
      (evalCrepRuntimeExp state right).bind (fun rightValue =>
          some (state.memoryModel.compare operator leftValue rightValue))) := by
  simp [evalCrepRuntimeExp]

private theorem evalCrepRuntimeExp_shift_raw
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (operator : Shift)
    (left right : CrepExp α) :
    evalCrepRuntimeExp state (.shift operator left right) =
      (evalCrepRuntimeExp state left).bind (fun leftValue =>
      (evalCrepRuntimeExp state right).bind (fun rightValue =>
          state.memoryModel.shift operator leftValue rightValue)) := by
  simp [evalCrepRuntimeExp]

theorem evalCrepRuntimeExp_cmp_riscvWordTarget_evalPanCmp [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : Cmp) (left right : CrepExp (RiscV.Word width)) :
    evalCrepRuntimeExp (riscvCrepWordTarget base) (.cmp operator left right) =
      (evalCrepRuntimeExp (riscvCrepWordTarget base) left).bind
        (fun leftValue =>
            (evalCrepRuntimeExp (riscvCrepWordTarget base) right).bind
              (fun rightValue => some (evalPanCmp operator leftValue rightValue))) := by
  rw [evalCrepRuntimeExp_cmp_raw]
  simp [riscvCrepWordTarget, RiscV.panRiscVMemoryModelForEndian,
    panRiscVCmp_eq_evalPanCmp]

theorem evalCrepRuntimeExp_shift_riscvWordTarget_evalPanShift [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : Shift) (left right : CrepExp (RiscV.Word width)) :
    evalCrepRuntimeExp (riscvCrepWordTarget base) (.shift operator left right) =
      (evalCrepRuntimeExp (riscvCrepWordTarget base) left).bind
        (fun leftValue =>
          (evalCrepRuntimeExp (riscvCrepWordTarget base) right).bind
            (fun rightValue => evalPanShiftFull operator leftValue rightValue)) := by
  rw [evalCrepRuntimeExp_shift_raw]
  simp [riscvCrepWordTarget, RiscV.panRiscVMemoryModelForEndian,
    panRiscVShift_eq_evalPanShiftFull]

theorem evalCrepRuntimeExp_cmp_riscvWordTarget_wordLab [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : Cmp) (left right : CrepExp (RiscV.Word width)) :
    (evalCrepRuntimeExp (riscvCrepWordTarget base) (.cmp operator left right)).map
      PanWordLab.word =
      (evalCrepRuntimeExp (riscvCrepWordTarget base) left).bind
        (fun leftValue =>
          (evalCrepRuntimeExp (riscvCrepWordTarget base) right).bind
            (fun rightValue => some (.word (evalPanCmp operator leftValue rightValue)))) := by
  rw [evalCrepRuntimeExp_cmp_riscvWordTarget_evalPanCmp]
  simp [Option.map_bind, Function.comp_def]

theorem evalCrepRuntimeExp_shift_riscvWordTarget_wordLab [NeZero width]
    (base : CrepRuntimeState (RiscV.Word width) σ)
    (operator : Shift) (left right : CrepExp (RiscV.Word width)) :
    (evalCrepRuntimeExp (riscvCrepWordTarget base) (.shift operator left right)).map
      PanWordLab.word =
      (evalCrepRuntimeExp (riscvCrepWordTarget base) left).bind
        (fun leftValue =>
          (evalCrepRuntimeExp (riscvCrepWordTarget base) right).bind
            (fun rightValue =>
              (evalPanShiftFull operator leftValue rightValue).map PanWordLab.word)) := by
  rw [evalCrepRuntimeExp_shift_riscvWordTarget_evalPanShift]
  simp [Option.map_bind, Function.comp_def]

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

/-! ## The RV64 `Op` evaluator case

HOL `crepSem$eval` evaluates `Op op args` by evaluating every argument and then
applying `word_op` (`cakeml/pancake/semantics/crepSemScript.sml:90-137` and
`cakeml/compiler/backend/wordLangScript.sml:302-311`).  For constant operands the
argument list evaluates to exactly those words, so the production RV64 evaluator
returns the HOL folded word.  Untagged until the whole evaluator correspondence
is reviewed; direct oracle `scripts/hol-probes/crep_eval_op_rv64_probe.out`
(`eval_op_add_const=SOME (Word 7w)`, `eval_op_sub_const=SOME (Word 5w)`,
`eval_op_and_const=SOME (Word 48w)`, `eval_op_add_empty=SOME (Word 0w)`,
`eval_op_sub_arity=NONE`). -/
theorem evalCrepRuntimeExp_op_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : BinOp) (values : List (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.op operator (values.map CrepExp.const)) =
      wordOpHOL operator values := by
  have hmapM : List.mapM (fun x : RiscV.Word 64 => some x) values = some values := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp [List.mapM_cons, ih]
  simp [evalCrepRuntimeExp, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel,
    RiscV.panRiscVWordOp, wordOpHOL, Function.comp_def, hmapM]

theorem evalCrepRuntimeExpWordLab_op_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : BinOp) (values : List (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base)
        (.op operator (values.map CrepExp.const)) =
      (wordOpHOL operator values).map PanWordLab.word := by
  have hmapM : List.mapM (fun x : RiscV.Word 64 => some x) values = some values := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp [List.mapM_cons, ih]
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel, RiscV.panRiscVWordOp,
    wordOpHOL, Function.comp_def, hmapM]

/-! ## The RV64 `Cmp` evaluator case

HOL `crepSem$eval` evaluates `Cmp op e1 e2` by evaluating both operands and then
applying `word_cmp` (`cakeml/pancake/semantics/crepSemScript.sml:90-137` and
`cakeml/compiler/encoders/asm/asmScript.sml:83`).  For constant operands the
production RV64 evaluator returns exactly the fixed target comparison
`RiscV.panRiscVCmp`; the remaining link from that primitive to HOL `word_cmp` is
the existing untagged `panRiscVCmp_eq_evalPanCmp` bridge, so no `@[hol]` tag is
attached yet.  Direct oracle `scripts/hol-probes/crep_eval_cmp_rv64_probe.out`
(`eval_cmp_equal_true=SOME (Word (v2w [T]))`, `eval_cmp_equal_false=SOME (Word (v2w [F]))`,
`eval_cmp_lower_true=SOME (Word (v2w [T]))`, `eval_cmp_test_zero=SOME (Word (v2w [F]))`,
`eval_cmp_test_disjoint=SOME (Word (v2w [T]))`). -/
theorem evalCrepRuntimeExp_cmp_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Cmp) (left right : RiscV.Word 64) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.cmp operator (.const left) (.const right)) =
      some (RiscV.panRiscVCmp operator left right) := by
  simp [evalCrepRuntimeExp, riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]

theorem evalCrepRuntimeExpWordLab_cmp_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Cmp) (left right : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base)
        (.cmp operator (.const left) (.const right)) =
      some (.word (RiscV.panRiscVCmp operator left right)) := by
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    riscv64CrepRuntimeTarget, RiscV.panRiscVMemoryModel]

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
`write_bytearray` is total: when `mem_store_byte` returns `NONE` it discards
that store *and every remaining store* and keeps the memory of the original
call. The production `crepRuntimeWriteBytes` mirrors this by returning the
original state on a `NONE` store. `riscv64SetMemory`/`riscv64WriteMem`
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
    head address after writing the tail.  A failed head store discards the tail
    writes too, returning the original state (HOL `write_bytearray`'s outer `m`). -/
theorem crepRuntimeWriteBytes_cons (s : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (byte : UInt8) (bytes : List UInt8) :
    crepRuntimeWriteBytes s address (byte :: bytes) =
      (crepRuntimeWriteBytes s (address + 1) bytes).map
        (fun tailState =>
          (crepRuntimeStoreByte tailState address (s.ffiContext.byteToWord byte)).getD
            s) := by
  rw [crepRuntimeWriteBytes]
  cases hrec : crepRuntimeWriteBytes s (address + 1) bytes with
  | none => rfl
  | some tailState =>
      simp [Option.getD]
      cases crepRuntimeStoreByte tailState address (s.ffiContext.byteToWord byte) <;> rfl

/-- HOL `write_bytearray address bytes memory domain false` for the canonical
    RISC-V 64 target: writes the bytes tail-first (matching HOL); a failed byte
    store discards the tail writes and returns the original canonical target. -/
def riscv64WriteState (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) : List UInt8 → CrepRuntimeState (RiscV.Word 64) σ
  | [] => riscv64CrepRuntimeTarget base
  | byte :: bytes =>
      (crepRuntimeStoreByte (riscv64WriteState base (address + 1) bytes) address
        ((riscv64CrepRuntimeTarget base).ffiContext.byteToWord byte)).getD
        (riscv64CrepRuntimeTarget base)

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
    the canonical target writer and install the returned ffi) is pinned by
    `crepRuntimeExtCallValues_target_returned`; `crepRuntimeExtCallValues_target_dispatch`
    assembles both handler outcomes. -/
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
    (write-back) is pinned by `crepRuntimeExtCallValues_target_returned` and the
    two are assembled by `crepRuntimeExtCallValues_target_dispatch`. -/
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

/-- Dispatch when the `callFfi` handler reports a `returned` result (HOL
    `FFI_return`): the production step writes the returned bytes back into the
    canonical target with `crepRuntimeWriteBytes` and returns `Normal` with the
    updated ffi, matching `write_bytearray` plus the ffi update in `call_FFI`. -/
theorem crepRuntimeExtCallValues_target_returned
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8)
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes)
    (ffi : FfiState σ) (bytes : List UInt8)
    (hr : riscv64ExtCallCallFfiHandler
        (.extCall function configurationBytes arrayBytes :
          CrepRuntimeRequest (RiscV.Word 64)) base.ffi = .returned ffi bytes) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (.normal, riscv64WriteState { base with ffi := ffi } array bytes) := by
  unfold crepRuntimeExtCallValues
  simp only [riscv64CrepRuntimeTarget_ffiContext,
    riscv64PanValueFfiContext_valueToNat_eq_riscv,
    crepRuntimeReadBytes_target_eq_riscv, riscv64CrepRuntimeTarget_ffi, hc, ha, hr]
  erw [crepRuntimeWriteBytes_target_updateFfi]

/-- Assembled canonical-target dispatch of `crepRuntimeExtCallValues`.  With both
    argument reads succeeding, the production step case-splits on the Lean
    `callFfi` (HOL `call_FFI`) result exactly as the source semantics does:
    `FFI_return` writes the returned bytes back into the canonical target and
    installs the returned ffi (`Normal`), while `FFI_final` returns `FinalFFI`
    with the target state unchanged.  The failing-read branch is
    `crepRuntimeExtCallValues_target_error`, so this theorem together with that
    one covers every production `ExtCall` outcome. -/
theorem crepRuntimeExtCallValues_target_dispatch
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (configurationBytes arrayBytes : List UInt8)
    (hc : riscv64ReadByteArray base configuration configurationLength.toNat =
      some configurationBytes)
    (ha : riscv64ReadByteArray base array arrayLength.toNat = some arrayBytes) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
       | .returned ffi bytes =>
           (.normal, riscv64WriteState { base with ffi := ffi } array bytes)
       | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base)) := by
  cases hres : callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
  | returned ffi bytes =>
      exact crepRuntimeExtCallValues_target_returned base function
        configuration configurationLength array arrayLength configurationBytes
        arrayBytes hc ha ffi bytes (by
          rw [riscv64ExtCallCallFfiHandler_extCall, hres])
  | final event =>
      exact crepRuntimeExtCallValues_target_final base function
        configuration configurationLength array arrayLength configurationBytes
        arrayBytes hc ha event (by
          rw [riscv64ExtCallCallFfiHandler_extCall, hres])

/-- One-shot canonical-target dispatch of `crepRuntimeExtCallValues`: the whole
    production `ExtCall` step equals a `call_FFI`-shaped relation on the
    canonical target, covering every branch.  When either argument read fails the
    step returns `Error`; otherwise it case-splits on the Lean `callFfi` (HOL
    `call_FFI`) result: `FFI_return` writes the returned bytes back and installs
    the returned ffi (`Normal`), while `FFI_final` returns `FinalFFI` with the
    target state unchanged.  This is a single statement with no target-run or
    post-state premises, so it can be composed with a source-side `call_FFI`
    relation directly. -/
theorem crepRuntimeExtCallValues_target_dispatch_any
    (base : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64) :
    crepRuntimeExtCallValues riscv64ExtCallCallFfiHandler
        (riscv64CrepRuntimeTarget base) function
        configuration configurationLength array arrayLength =
      (match riscv64ReadByteArray base configuration configurationLength.toNat,
             riscv64ReadByteArray base array arrayLength.toNat with
       | some configurationBytes, some arrayBytes =>
           (match callFfi base.ffi (.extCall function) configurationBytes arrayBytes with
            | .returned ffi bytes =>
                (.normal, riscv64WriteState { base with ffi := ffi } array bytes)
            | .final event => (.finalFfi event, riscv64CrepRuntimeTarget base))
       | _, _ => (.error, riscv64CrepRuntimeTarget base)) := by
  cases hc : riscv64ReadByteArray base configuration configurationLength.toNat with
  | none =>
      exact crepRuntimeExtCallValues_target_error base function configuration
        configurationLength array arrayLength (Or.inl hc)
  | some configurationBytes =>
      cases ha : riscv64ReadByteArray base array arrayLength.toNat with
      | none =>
          exact crepRuntimeExtCallValues_target_error base function configuration
            configurationLength array arrayLength (Or.inr ha)
      | some arrayBytes =>
          exact crepRuntimeExtCallValues_target_dispatch base function
            configuration configurationLength array arrayLength configurationBytes
            arrayBytes hc ha

/-! ## Post-write-back memory correspondence

HOL `write_bytearray` updates the source `word_lab` memory by storing each
returned byte with `mem_store_byte`. The canonical target `riscv64WriteState`
performs the same tail-first recursion with `crepRuntimeStoreByte`. The two
agree on the `PanValue.word` view recorded by `stateRel` for every `memaddrs`
domain: when a byte store fails, both HOL `write_bytearray` and the production
writer fall back to the original memory (HOL's outer `m`), so the
correspondence holds for successful and failed stores alike. -/

/-- The source `PanValue` view of a total `word_lab` target memory: the
    `stateRel` memory conjunct written as a named function. -/
def panValueMemoryView (memory : α → PanWordLab α) : α → Option (PanValue α) :=
  fun address => some (.word (panTheWord (memory address)))

/-- Wrap the raw word cells of a memory view back into `PanValue.word`. -/
def panValueViewOf (raw : α → Option α) : α → Option (PanValue α) :=
  fun address => (raw address).map PanValue.word

theorem panValueMemoryView_eq_panValueViewOf (memory : α → PanWordLab α) :
    panValueMemoryView memory = panValueViewOf (crepRuntimeMemoryView memory) := rfl

/-- The store bridge over an arbitrary tail memory: the production byte store
    equals the canonical RISC-V store as a memory view. -/
theorem crepRuntimeStoreByte_setMemory_view
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (address value : RiscV.Word 64) :
    (crepRuntimeStoreByte (riscv64SetMemory base memory) address value).map
        (fun state => crepRuntimeMemoryView state.memory) =
      RiscV.panRiscVStoreByte base.memaddrs (crepRuntimeMemoryView memory)
        (8 : RiscV.Word 64) address value := by
  rw [crepRuntimeStoreByte_eq_memory_view]
  simp only [riscv64SetMemory, riscv64CrepRuntimeTarget, RiscV.panRiscVStoreByte,
    panModelStoreByte, RiscV.panRiscVMemoryModel]
  by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address) = true
  · simp only [hb, if_true, crepRuntimeMemoryView, Option.pure_def, panTheWord]
    rw [updateMemory_eq_panModelUpdateMemory]
    rfl
  · simp only [hb, if_false, Bool.false_eq_true]

/-- The canonical source byte store on the `PanValue` view equals the wrap of the
    canonical RISC-V store. -/
theorem panValueStoreByte_view
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (address value : RiscV.Word 64) :
    (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs).storeByte
        base.memaddrs (panValueMemoryView memory) (8 : RiscV.Word 64) address value =
      (RiscV.panRiscVStoreByte base.memaddrs (crepRuntimeMemoryView memory)
        (8 : RiscV.Word 64) address value).map panValueViewOf := by
  rw [← crepRuntimeStoreByte_setMemory_view, Option.map_map]
  simp only [panValueMemoryAccessOfModel, panValueMemoryView, riscv64SetMemory,
    crepRuntimeStoreByte, RiscV.panRiscVMemoryModel, riscv64CrepRuntimeTarget]
  by_cases hb : base.memaddrs (RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address) = true
  · simp only [hb, if_true, Option.map_some,
      Option.pure_def, Function.comp_apply]
    have hfun :
        (fun current : RiscV.Word 64 =>
            if (current == RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address) = true then
              some (PanValue.word (RiscV.panRiscVSetByte (8 : RiscV.Word 64) address value
                (panTheWord (memory (RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address)))))
            else some (PanValue.word (panTheWord (memory current)))) =
          panValueViewOf (crepRuntimeMemoryView
            (updateCrepRuntimeMemory memory (RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address)
              (PanWordLab.word (RiscV.panRiscVSetByte (8 : RiscV.Word 64) address value
                (panTheWord (memory (RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address))))))) := by
      funext current
      by_cases h : current = RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address <;>
        simp_all [updateCrepRuntimeMemory, panValueViewOf, crepRuntimeMemoryView, panTheWord]
    rw [← hfun]
    rfl
  · simp only [hb, if_false, Bool.false_eq_true]
    rfl

/-- A successful production byte store agrees with the tail on every field other
    than memory. -/
theorem crepRuntimeStoreByte_some_eq [BEq α] [Add α] [OfNat α 1]
    {s : CrepRuntimeState α σ} {address value : α}
    {u : CrepRuntimeState α σ} (h : crepRuntimeStoreByte s address value = some u) :
    u = { s with memory := u.memory } := by
  unfold crepRuntimeStoreByte at h
  dsimp only at h
  split at h
  · injection h with h; subst h; rfl
  · simp at h

/-- The production byte store does not depend on the ffi state, so updating the
    ffi is commuted with the store (the updated state keeps the same ffi). -/
theorem crepRuntimeStoreByte_withFfi [BEq α] [Add α] [OfNat α 1]
    (s : CrepRuntimeState α σ) (ffi : FfiState σ) (address value : α) :
    crepRuntimeStoreByte { s with ffi := ffi } address value =
      (crepRuntimeStoreByte s address value).map (fun u => { u with ffi := ffi }) := by
  unfold crepRuntimeStoreByte
  by_cases h : s.memaddrs (s.memoryModel.byteAlign s.bytesInWord address) = true
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false, Bool.false_eq_true]
    rfl

/-- Updating the ffi before writing bytes commutes with the write on every field:
    the resulting write state is the canonical write state with the new ffi
    installed (the written memory is independent of the ffi). -/
theorem riscv64WriteState_withFfi (base : CrepRuntimeState (RiscV.Word 64) σ)
    (ffi : FfiState σ) (address : RiscV.Word 64) (bytes : List UInt8) :
    riscv64WriteState { base with ffi := ffi } address bytes =
      { riscv64WriteState base address bytes with ffi := ffi } := by
  induction bytes generalizing address with
  | nil => rfl
  | cons byte bytes ih =>
      rw [riscv64WriteState, ih (address + 1), riscv64WriteState]
      rw [riscv64CrepRuntimeTarget_withFfi]
      erw [crepRuntimeStoreByte_withFfi]
      cases crepRuntimeStoreByte (riscv64WriteState base (address + 1) bytes) address
          ((riscv64CrepRuntimeTarget base).ffiContext.byteToWord byte) <;> rfl

/-- `riscv64WriteState` only changes memory, so it is the canonical target with
    its own resulting memory installed. -/
theorem riscv64WriteState_eq_setMemory
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (bytes : List UInt8) :
    riscv64WriteState base address bytes =
      riscv64SetMemory base (riscv64WriteState base address bytes).memory := by
  induction bytes generalizing address with
  | nil => rfl
  | cons byte bytes ih =>
      rw [riscv64WriteState]
      cases hstore : crepRuntimeStoreByte (riscv64WriteState base (address + 1) bytes)
          address ((riscv64CrepRuntimeTarget base).ffiContext.byteToWord byte) with
      | none =>
          simp only [Option.getD_none]
          exact (riscv64SetMemory_self base).symm
      | some u =>
          simp only [Option.getD_some]
          rw [crepRuntimeStoreByte_some_eq hstore, ih (address + 1)]
          rfl

/-- The `PanValue` view of the target store result (with the HOL total fallback)
    is the `panValueViewOf` image of the canonical RISC-V store, with the
    original view as fallback. -/
theorem crepRuntimeStoreByte_getD_view
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (address value : RiscV.Word 64) :
    panValueMemoryView
        ((crepRuntimeStoreByte (riscv64SetMemory base memory) address value).getD
          (riscv64CrepRuntimeTarget base)).memory =
      ((RiscV.panRiscVStoreByte base.memaddrs (crepRuntimeMemoryView memory)
        (8 : RiscV.Word 64) address value).map panValueViewOf).getD
        (panValueMemoryView base.memory) := by
  have hview := crepRuntimeStoreByte_setMemory_view base memory address value
  cases hT : crepRuntimeStoreByte (riscv64SetMemory base memory) address value with
  | none =>
      rw [hT] at hview
      simp only [Option.map_none] at hview
      rw [← hview]
      simp only [Option.map_none, Option.getD_none, riscv64CrepRuntimeTarget]
  | some u =>
      rw [hT] at hview
      simp only [Option.map_some] at hview
      rw [← hview]
      simp only [Option.map_some, Option.getD_some,
        panValueMemoryView_eq_panValueViewOf]

/-- The canonical source byte-array write and the canonical target
    `riscv64WriteState` agree on the `PanValue.word` view for every memory
    domain: a failed byte store falls back to the original memory on both sides,
    matching HOL `write_bytearray`. -/
theorem panSemWriteBytearray_target_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (bytes : List UInt8) :
    panSemWriteBytearray
        (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
        (riscv64PanValueFfiContext base.shMemaddrs)
        (panValueMemoryView base.memory) (8 : RiscV.Word 64) address bytes =
      panValueMemoryView ((riscv64WriteState base address bytes).memory) := by
  induction bytes generalizing address with
  | nil => simp [panSemWriteBytearray, riscv64WriteState, riscv64CrepRuntimeTarget]
  | cons byte bytes ih =>
      rw [panSemWriteBytearray, ih (address + 1)]
      conv =>
        rhs
        rw [riscv64WriteState, riscv64WriteState_eq_setMemory base (address + 1) bytes]
      simp only [riscv64CrepRuntimeTarget_ffiContext]
      erw [panValueStoreByte_view]
      rw [crepRuntimeStoreByte_getD_view]
      cases RiscV.panRiscVStoreByte base.memaddrs
          (crepRuntimeMemoryView ((riscv64WriteState base (address + 1) bytes).memory))
          (8 : RiscV.Word 64) address
          ((riscv64PanValueFfiContext base.shMemaddrs).byteToWord byte) <;> rfl

/-- The source `panValueFfiWriteBytes` is the same definition as the
    `panSemWriteBytearray` boundary. -/
theorem panValueFfiWriteBytes_eq_panSemWriteBytearray
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord address : α)
    (bytes : List UInt8) :
    panValueFfiWriteBytes access context memory bytesInWord address bytes =
      panSemWriteBytearray access context memory bytesInWord address bytes := by
  induction bytes generalizing address with
  | nil => simp [panValueFfiWriteBytes, panSemWriteBytearray]
  | cons byte bytes ih =>
      simp only [panValueFfiWriteBytes, panSemWriteBytearray, ih]
      cases access.storeByte access.domain
        (panSemWriteBytearray access context memory bytesInWord (address + 1) bytes)
        bytesInWord address (context.byteToWord byte) <;> rfl

/-- The source `panValueFfiReadBytes` on the `PanValue` view of the canonical
    target memory is the canonical RISC-V `riscv64ReadByteArray` (HOL
    `read_bytearray`). -/
theorem panValueFfiReadBytes_view_eq_riscv
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (length : Nat) :
    panValueFfiReadBytes
        (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel base.memaddrs)
        (riscv64PanValueFfiContext base.shMemaddrs)
        (panValueMemoryView base.memory) (8 : RiscV.Word 64) address length =
      riscv64ReadByteArray base address length := by
  induction length generalizing address with
  | zero => simp [panValueFfiReadBytes, riscv64ReadByteArray]
  | succ n ih =>
      simp only [panValueFfiReadBytes, riscv64ReadByteArray]
      rw [ih (address + 1)]
      simp only [panValueMemoryAccessOfModel, panValueWordMemory, panValueMemoryView,
        crepRuntimeMemoryView, riscv64PanValueFfiContext, RiscV.panRiscVReadByte,
        RiscV.panRiscVMemoryModel, panModelReadByte]

/-! ## Shared-memory FFI dispatch

HOL `panSem$sh_mem_load`/`sh_mem_store` (and the `crepSem$sh_mem_load`/`sh_mem_store`
counterparts) dispatch a shared-memory access through
`call_FFI s.ffi (SharedMem MappedRead/MappedWrite) [n2w width] payload`, where the
width is the operation size and the payload is the address (reads) or the value
bytes followed by the address bytes (writes). The canonical RISC-V 64 target
below installs the matching request handler and the address/width lemmas, so the
production `crepRuntimeSharedMem` step is the HOL rule once the source outcome is
fixed. Direct oracle: `scripts/hol-probes/crep_runtime_shared_mem_probe.out`. -/

/-- The `FfiShmemOp` selected by a Crep shared-memory operator (HOL `sh_mem_op`). -/
def crepSharedMemOperator : CrepMemOp → FfiShmemOp
  | .load | .load8 | .load16 | .load32 => .mappedRead
  | .store | .store8 | .store16 | .store32 => .mappedWrite

/-- HOL `sh_mem_op` read case: an `OpSize` becomes the Crep load operator. -/
def opSizeToCrepLoadOp : OpSize → CrepMemOp
  | .opW => .load
  | .op8 => .load8
  | .op16 => .load16
  | .op32 => .load32

/-- HOL `sh_mem_op` store case: an `OpSize` becomes the Crep store operator. -/
def opSizeToCrepStoreOp : OpSize → CrepMemOp
  | .opW => .store
  | .op8 => .store8
  | .op16 => .store16
  | .op32 => .store32

@[simp] theorem crepRuntimeMemWidth_opSizeToCrepLoadOp (size : OpSize) :
    crepRuntimeMemWidth (opSizeToCrepLoadOp size) = panValueFfiWidth size := by
  cases size <;> rfl

@[simp] theorem crepRuntimeMemWidth_opSizeToCrepStoreOp (size : OpSize) :
    crepRuntimeMemWidth (opSizeToCrepStoreOp size) = panValueFfiWidth size := by
  cases size <;> rfl

/-- The canonical target aligns a shared-memory read exactly as the HOL source
    side does (`sh_mem_op`/`byte_align`). -/
theorem crepRuntimeSharedAddress_opSizeToCrepLoadOp
    (base : CrepRuntimeState (RiscV.Word 64) σ) (size : OpSize)
    (address : RiscV.Word 64) :
    crepRuntimeSharedAddress (riscv64CrepRuntimeTarget base)
        (opSizeToCrepLoadOp size) address =
      panValueFfiSharedAddress (riscv64PanValueFfiContext base.shMemaddrs)
        size address := by
  unfold crepRuntimeSharedAddress panValueFfiSharedAddress
  rw [crepRuntimeMemWidth_opSizeToCrepLoadOp]
  by_cases h : panValueFfiWidth size = 0 <;>
    simp [h, riscv64CrepRuntimeTarget, riscv64PanValueFfiContext, RiscV.panRiscVMemoryModel]

/-- Canonical target alignment for the shared-memory store operators. -/
theorem crepRuntimeSharedAddress_opSizeToCrepStoreOp
    (base : CrepRuntimeState (RiscV.Word 64) σ) (size : OpSize)
    (address : RiscV.Word 64) :
    crepRuntimeSharedAddress (riscv64CrepRuntimeTarget base)
        (opSizeToCrepStoreOp size) address =
      panValueFfiSharedAddress (riscv64PanValueFfiContext base.shMemaddrs)
        size address := by
  unfold crepRuntimeSharedAddress panValueFfiSharedAddress
  rw [crepRuntimeMemWidth_opSizeToCrepStoreOp]
  by_cases h : panValueFfiWidth size = 0 <;>
    simp [h, riscv64CrepRuntimeTarget, riscv64PanValueFfiContext, RiscV.panRiscVMemoryModel]

/-- The canonical shared-memory request handler: a `sharedMem` request dispatches
    to the Lean `callFfi` (the `call_FFI` port) with the HOL `SharedMem` name, the
    width byte, and the payload, mapping its `FfiResult` to the Crep handler
    response. The `extCall` case is dead for the shared-memory relation and just
    returns the unchanged ffi. -/
def riscv64SharedMemCallFfiHandler :
    CrepRuntimeFfiHandler α σ FfiFinalEvent
  | .sharedMem operator _name _address payload, ffi =>
      match callFfi ffi (.sharedMem (crepSharedMemOperator operator))
          [UInt8.ofNat (crepRuntimeMemWidth operator)] payload with
      | .returned nextFfi bytes => .returned nextFfi bytes
      | .final event => .final event
  | .extCall _ _ _, ffi => .returned ffi []

/-- The canonical shared-memory handler characterises the `sharedMem` request
    exactly as HOL `call_FFI (SharedMem ...)`. -/
theorem riscv64SharedMemCallFfiHandler_sharedMem
    (operator : CrepMemOp) (name : Nat) (address : RiscV.Word 64)
    (payload : List UInt8) (ffi : FfiState σ) :
    riscv64SharedMemCallFfiHandler
        (.sharedMem operator name address payload :
          CrepRuntimeRequest (RiscV.Word 64)) ffi =
      (match callFfi ffi (.sharedMem (crepSharedMemOperator operator))
          [UInt8.ofNat (crepRuntimeMemWidth operator)] payload with
       | .returned nextFfi bytes => .returned nextFfi bytes
       | .final event => .final event) := rfl

/-- The canonical target accepts exactly the HOL source shared-memory domain:
    the `memaddrs`-style validity bit is the source `sharedDomain` of the
    aligned address. -/
theorem crepRuntimeSharedAddressValid_opSizeToCrepLoadOp
    (base : CrepRuntimeState (RiscV.Word 64) σ) (size : OpSize)
    (address : RiscV.Word 64) :
    crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
        (opSizeToCrepLoadOp size) address =
      (riscv64PanValueFfiContext base.shMemaddrs).sharedDomain
        (panValueFfiSharedAddress (riscv64PanValueFfiContext base.shMemaddrs)
          size address) := by
  unfold crepRuntimeSharedAddressValid
  rw [crepRuntimeSharedAddress_opSizeToCrepLoadOp]
  rfl

/-- Store-operator form of the canonical shared-memory validity bridge. -/
theorem crepRuntimeSharedAddressValid_opSizeToCrepStoreOp
    (base : CrepRuntimeState (RiscV.Word 64) σ) (size : OpSize)
    (address : RiscV.Word 64) :
    crepRuntimeSharedAddressValid (riscv64CrepRuntimeTarget base)
        (opSizeToCrepStoreOp size) address =
      (riscv64PanValueFfiContext base.shMemaddrs).sharedDomain
        (panValueFfiSharedAddress (riscv64PanValueFfiContext base.shMemaddrs)
          size address) := by
  unfold crepRuntimeSharedAddressValid
  rw [crepRuntimeSharedAddress_opSizeToCrepStoreOp]
  rfl

/-- The target shared-memory store payload for the canonical target is the
    source `panValueFfiSharedStore` payload, so the `callFfi` request coincides:
    the width byte and the value/address byte concatenation agree. -/
theorem crepRuntimeSharedStorePayload_eq
    (context : PanValueFfiContext (RiscV.Word 64))
    (value address : RiscV.Word 64) (size : OpSize) :
    (if crepRuntimeMemWidth (opSizeToCrepStoreOp size) = 0 then
        context.wordToBytes value false ++ context.wordToBytes address false
      else
        (context.wordToBytes value false).take
            (crepRuntimeMemWidth (opSizeToCrepStoreOp size)) ++
          context.wordToBytes address false)
      =
    (if panValueFfiWidth size = 0 then
        context.wordToBytes value false ++ context.wordToBytes address false
      else
        (context.wordToBytes value false).take (panValueFfiWidth size) ++
          context.wordToBytes address false) := by
  cases size <;> simp [crepRuntimeMemWidth, opSizeToCrepStoreOp, panValueFfiWidth]

/-! ## Configuration stability

`isRiscV64CrepRuntimeTarget` is the canonical configuration. The production
transitions proved below update only `locals`, `memory`, `globals`, `clock`, or
`ffi`, leaving the configuration fields unchanged. These lemmas make the
HOL-shaped memory and FFI bridges reusable at the covered transition
boundaries; preservation by the entire evaluator remains part of the
correctness proof.

The pinned values are exactly the HOL word-type values: on 64-bit words
`byte$bytes_in_word = dimindex (:'a) DIV 8 = 8`
(`scripts/hol-probes/crep_runtime_word_boundary_probe.out`: `bytes64=8w`,
`bytes32=4w`), and `byte_align` coincides with `RiscV.panRiscVByteAlign 8`
(`scripts/hol-probes/crep_runtime_shared_domain_probe.out`: `align_9=8w`,
`align_16=16w`). Nothing here changes a tagged declaration or adds a premise to
one; the target stays an ordinary predicate and `stateRel` is untouched. -/

/-- A state that agrees with a configured state on the four configuration
    fields (and on `shMemaddrs`, which the FFI context is read from) stays
    configured. -/
theorem isRiscV64CrepRuntimeTarget_of_components {state u : CrepRuntimeState (RiscV.Word 64) σ}
    (h : isRiscV64CrepRuntimeTarget state)
    (hs : u.shMemaddrs = state.shMemaddrs)
    (hb : u.bytesInWord = state.bytesInWord)
    (he : u.bigEndian = state.bigEndian)
    (hm : u.memoryModel = state.memoryModel)
    (hf : u.ffiContext = state.ffiContext) :
    isRiscV64CrepRuntimeTarget u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hb.trans h1, he.trans h2, hm.trans h3,
    (hf.trans h4).trans (congrArg riscv64PanValueFfiContext hs.symm)⟩

/-- Updating the memory preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_updateMemory {state : CrepRuntimeState (RiscV.Word 64) σ}
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget { state with memory := memory } :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- Updating the locals preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_updateLocals {state : CrepRuntimeState (RiscV.Word 64) σ}
    (locals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget { state with locals := locals } :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- Updating the globals preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_updateGlobals {state : CrepRuntimeState (RiscV.Word 64) σ}
    (globals : BitVec 5 → Option (PanWordLab (RiscV.Word 64)))
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget { state with globals := globals } :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- Updating the FFI state preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_updateFfi {state : CrepRuntimeState (RiscV.Word 64) σ}
    (ffi : FfiState σ) (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget { state with ffi := ffi } :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- Updating the FFI state and then the locals preserves the canonical
    configuration. This is the shape of the shared-memory load write-back. -/
theorem isRiscV64CrepRuntimeTarget_updateFfiLocals {state : CrepRuntimeState (RiscV.Word 64) σ}
    (ffi : FfiState σ) (locals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget { { state with ffi := ffi } with locals := locals } :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- `dec_clock` preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_decCrepClock {state : CrepRuntimeState (RiscV.Word 64) σ}
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget (decCrepClock state) :=
  isRiscV64CrepRuntimeTarget_of_components h rfl rfl rfl rfl rfl

/-- Writing a local preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_updateCrepRuntimeLocal
    {state : CrepRuntimeState (RiscV.Word 64) σ} {name : Nat}
    {value : PanWordLab (RiscV.Word 64)} (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget
      { state with locals := updateCrepRuntimeLocal state.locals name value } :=
  isRiscV64CrepRuntimeTarget_updateLocals _ h

/-- Clearing the locals preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_clearCrepRuntimeLocals
    {state : CrepRuntimeState (RiscV.Word 64) σ} (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget (clearCrepRuntimeLocals state) :=
  isRiscV64CrepRuntimeTarget_updateLocals _ h

/-- Writing a global preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_setCrepRuntimeGlobals
    {state : CrepRuntimeState (RiscV.Word 64) σ} {key : BitVec 5}
    {value : PanWordLab (RiscV.Word 64)} (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget (setCrepRuntimeGlobals key value state) :=
  isRiscV64CrepRuntimeTarget_updateGlobals _ h

/-- A successful plain store preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeStore
    {state : CrepRuntimeState (RiscV.Word 64) σ} {address value : RiscV.Word 64}
    (h : isRiscV64CrepRuntimeTarget state) :
    ∀ u, crepRuntimeStore state address value = some u → isRiscV64CrepRuntimeTarget u := by
  intro u hu
  unfold crepRuntimeStore at hu
  split at hu
  · injection hu with hu
    subst hu
    exact isRiscV64CrepRuntimeTarget_updateMemory _ h
  · simp at hu

/-- A successful byte store preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeStoreByte
    {state : CrepRuntimeState (RiscV.Word 64) σ} {address value : RiscV.Word 64}
    (h : isRiscV64CrepRuntimeTarget state) :
    ∀ u, crepRuntimeStoreByte state address value = some u → isRiscV64CrepRuntimeTarget u := by
  intro u hu
  unfold crepRuntimeStoreByte at hu
  dsimp only at hu
  split at hu
  · injection hu with hu
    subst hu
    exact isRiscV64CrepRuntimeTarget_updateMemory _ h
  · simp at hu

/-- A successful 32-bit store preserves the canonical configuration. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeStore32
    {state : CrepRuntimeState (RiscV.Word 64) σ} {address value : RiscV.Word 64}
    (h : isRiscV64CrepRuntimeTarget state) :
    ∀ u, crepRuntimeStore32 state address value = some u → isRiscV64CrepRuntimeTarget u := by
  intro u hu
  unfold crepRuntimeStore32 at hu
  dsimp only at hu
  split at hu
  · split at hu
    · injection hu with hu
      subst hu
      exact isRiscV64CrepRuntimeTarget_updateMemory _ h
    · simp at hu
  · simp at hu

/-- The canonical target's memory-only variant is configured. -/
theorem isRiscV64CrepRuntimeTarget_riscv64SetMemory
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64)) :
    isRiscV64CrepRuntimeTarget (riscv64SetMemory base memory) :=
  isRiscV64CrepRuntimeTarget_updateMemory memory (riscv64CrepRuntimeTarget_isTarget base)

/-- The HOL `write_bytearray` state is configured for every base state, since it
    only replaces the memory of the canonical target. -/
theorem isRiscV64CrepRuntimeTarget_riscv64WriteState
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64)
    (bytes : List UInt8) :
    isRiscV64CrepRuntimeTarget (riscv64WriteState base address bytes) := by
  induction bytes generalizing address with
  | nil => exact riscv64CrepRuntimeTarget_isTarget base
  | cons byte bytes ih =>
      rw [riscv64WriteState]
      cases hstore : crepRuntimeStoreByte (riscv64WriteState base (address + 1) bytes)
          address ((riscv64CrepRuntimeTarget base).ffiContext.byteToWord byte) with
      | none =>
          rw [Option.getD_none]
          exact riscv64CrepRuntimeTarget_isTarget base
      | some u =>
          rw [Option.getD_some]
          exact isRiscV64CrepRuntimeTarget_crepRuntimeStoreByte (ih (address + 1)) u hstore

/-- A successful production byte-array write preserves the canonical
    configuration. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeWriteBytes
    {state : CrepRuntimeState (RiscV.Word 64) σ} {address : RiscV.Word 64}
    {bytes : List UInt8} (h : isRiscV64CrepRuntimeTarget state) :
    ∀ u, crepRuntimeWriteBytes state address bytes = some u → isRiscV64CrepRuntimeTarget u := by
  induction bytes generalizing address with
  | nil =>
      intro u hu
      simp only [crepRuntimeWriteBytes, Option.some.injEq] at hu
      subst hu
      exact h
  | cons byte bytes ih =>
      intro u hu
      rw [crepRuntimeWriteBytes_cons] at hu
      cases ht : crepRuntimeWriteBytes state (address + 1) bytes with
      | none => rw [ht] at hu; simp at hu
      | some tail =>
          have htail : isRiscV64CrepRuntimeTarget tail := ih (address := address + 1) tail ht
          rw [ht] at hu
          simp only [Option.map_some] at hu
          cases hs : crepRuntimeStoreByte tail address (state.ffiContext.byteToWord byte) with
          | none =>
              rw [hs] at hu
              simp only [Option.getD_none, Option.some.injEq] at hu
              subst hu
              exact h
          | some updated =>
              rw [hs] at hu
              simp only [Option.getD_some, Option.some.injEq] at hu
              subst hu
              exact isRiscV64CrepRuntimeTarget_crepRuntimeStoreByte htail updated hs

/-- A shared-memory operation preserves the canonical configuration: every
    result state is either `state` (error/final), an ffi-only update, or an
    ffi update plus a local write-back (the load `returned` case). -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeSharedMem
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ ε)
    {state : CrepRuntimeState (RiscV.Word 64) σ}
    (operator : CrepMemOp) (name : Nat) (address : RiscV.Word 64)
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget
      (crepRuntimeSharedMem handler state operator name address).2 := by
  unfold crepRuntimeSharedMem
  repeat' first
    | exact isRiscV64CrepRuntimeTarget_updateFfiLocals _ _ h
    | exact isRiscV64CrepRuntimeTarget_clearCrepRuntimeLocals h
    | exact isRiscV64CrepRuntimeTarget_updateFfi _ h
    | exact h
    | split
    | (simp only []; split)

/-- The production ExtCall value dispatch preserves the canonical
    configuration: on `returned` it is an ffi update followed by
    `crepRuntimeWriteBytes`, otherwise it is `state`. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeExtCallValues
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ ε)
    {state : CrepRuntimeState (RiscV.Word 64) σ} (function : FunName)
    (configuration configurationLength array arrayLength : RiscV.Word 64)
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget
      (crepRuntimeExtCallValues handler state function configuration
        configurationLength array arrayLength).2 := by
  simp only [crepRuntimeExtCallValues]
  cases hc : crepRuntimeReadBytes state configuration
      (state.ffiContext.valueToNat configurationLength) with
  | none => exact h
  | some configurationBytes =>
      cases ha : crepRuntimeReadBytes state array
          (state.ffiContext.valueToNat arrayLength) with
      | none => exact h
      | some arrayBytes =>
          simp only []
          cases hh : handler (.extCall function configurationBytes arrayBytes) state.ffi with
          | returned ffi bytes =>
              simp only []
              cases hw : crepRuntimeWriteBytes { state with ffi := ffi } array bytes with
              | none => exact isRiscV64CrepRuntimeTarget_updateFfi ffi h
              | some u =>
                  exact isRiscV64CrepRuntimeTarget_crepRuntimeWriteBytes
                    (isRiscV64CrepRuntimeTarget_updateFfi ffi h) u hw
          | final event => exact h

/-- The four-local production ExtCall wrapper preserves the canonical
    configuration. -/
theorem isRiscV64CrepRuntimeTarget_crepRuntimeExtCall
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ ε)
    {state : CrepRuntimeState (RiscV.Word 64) σ} (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (h : isRiscV64CrepRuntimeTarget state) :
    isRiscV64CrepRuntimeTarget
      (crepRuntimeExtCall handler state function configuration configurationLength
        array arrayLength).2 := by
  simp only [crepRuntimeExtCall]
  cases h1 : state.locals configuration with
  | none => exact h
  | some c =>
      cases h2 : state.locals configurationLength with
      | none => exact h
      | some cl =>
          cases h3 : state.locals array with
          | none => exact h
          | some a =>
              cases h4 : state.locals arrayLength with
              | none => exact h
              | some al =>
                  exact isRiscV64CrepRuntimeTarget_crepRuntimeExtCallValues handler
                    function (panTheWord c) (panTheWord cl) (panTheWord a)
                    (panTheWord al) h

/-! ## HOL `get_byte`/`byte_align` bridge for the RV64 `LoadByte` evaluator case

HOL `panSem$mem_load_byte_def` reads the aligned cell and extracts a byte with
`byte$get_byte`/`byte$byte_align`, stated directly on the word type
(`dimindex(:'a) DIV 8` bytes per word).  The RISC-V model's `panRiscVGetByte`
uses base-256 arithmetic instead of HOL's shift, so the two only agree because
`256 ^ k = 2 ^ (8 * k)`.  The definitions below render the HOL primitives at
`Word 64` so the production evaluator's `LoadByte` case can be stated against
them.  All declarations here are untagged while the statement shape is under
review (bead `flapjack-pxn.18.4.3.48.1.2`). -/

/-- HOL `byte$byte_align` at `Word 64`: clear the low three bits. -/
def holByteAlign64 (address : RiscV.Word 64) : RiscV.Word 64 :=
  BitVec.ofNat 64 ((address.toNat / 8) * 8)

/-- HOL `byte$byte_index` at `Word 64` (little-endian when `bigEndian = false`). -/
def holByteIndex64 (address : RiscV.Word 64) (bigEndian : Bool) : Nat :=
  let d := 8
  if bigEndian then 8 * ((d - 1) - address.toNat % d) else 8 * (address.toNat % d)

/-- HOL `byte$get_byte` at `Word 64`, widened back to a word. -/
def holGetByte64 (address value : RiscV.Word 64) (bigEndian : Bool) : RiscV.Word 64 :=
  BitVec.ofNat 64 ((value.toNat >>> holByteIndex64 address bigEndian) % 256)

/-- HOL `panSem$mem_load_byte` at `Word 64` over a total `word -> word_lab`
memory viewed through `crepRuntimeMemoryView`. -/
def holMemLoadByte64 (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (bigEndian : Bool)
    (address : RiscV.Word 64) : Option (RiscV.Word 64) :=
  let aligned := holByteAlign64 address
  match memory aligned with
  | some value => if domain aligned then some (holGetByte64 address value bigEndian) else none
  | none => none

theorem panRiscVByteAlign_eight_eq_holByteAlign64 (address : RiscV.Word 64) :
    RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address = holByteAlign64 address := by
  simp [RiscV.panRiscVByteAlign, holByteAlign64]

theorem panRiscVByteIndex_eight (address : RiscV.Word 64) :
    RiscV.panRiscVByteIndex (8 : RiscV.Word 64) address = address.toNat % 8 := by
  simp [RiscV.panRiscVByteIndex]

theorem panRiscVGetByte_eight_eq_holGetByte64 (address value : RiscV.Word 64) :
    RiscV.panRiscVGetByte (8 : RiscV.Word 64) address value =
      holGetByte64 address value false := by
  rw [RiscV.panRiscVGetByte, panRiscVByteIndex_eight, holGetByte64, holByteIndex64]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  have hpow : (256 : Nat) ^ (BitVec.toNat address % 8) =
      2 ^ (8 * (BitVec.toNat address % 8)) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hpow, Nat.shiftRight_eq_div_pow]

theorem panRiscVReadByte_eight_eq_holMemLoadByte64
    (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (address : RiscV.Word 64) :
    RiscV.panRiscVReadByte domain memory (8 : RiscV.Word 64) address =
      holMemLoadByte64 domain memory false address := by
  simp only [RiscV.panRiscVReadByte, panModelReadByte, RiscV.panRiscVMemoryModel,
    panRiscVByteAlign_eight_eq_holByteAlign64, holMemLoadByte64,
    panRiscVGetByte_eight_eq_holGetByte64]
  by_cases hd : domain (holByteAlign64 address) = true <;>
    cases hm : memory (holByteAlign64 address) <;>
    simp_all

/-- The production `LoadByte` at the RV64 target equals HOL `mem_load_byte` over
the memory view.  This is the genuine evaluator-case bridge for the `LoadByte`
constructor with a constant address. -/
theorem crepRuntimeLoadByte_rv64_eq_holMemLoadByte64
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoadByte (riscv64CrepRuntimeTarget base) address =
      holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  rw [crepRuntimeLoadByte_target_eq_riscv, panRiscVReadByte_eight_eq_holMemLoadByte64]

/-- Evaluator case: `evalCrepRuntimeExp` of `LoadByte (Const address)` at the
RV64 target is exactly HOL `mem_load_byte`. -/
theorem evalCrepRuntimeExp_loadByte_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.loadByte (.const address)) =
      holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  simp [evalCrepRuntimeExp, crepRuntimeLoadByte_rv64_eq_holMemLoadByte64]

/-- Word_lab evaluator case: the production word_lab core's `LoadByte (Const
address)` at the RV64 target is HOL `mem_load_byte` wrapped in `PanWordLab.word`. -/
theorem evalCrepRuntimeExpWordLab_loadByte_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base) (.loadByte (.const address)) =
      (holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address).map
        PanWordLab.word := by
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    crepRuntimeLoadByte_rv64_eq_holMemLoadByte64]

/-- HOL-shaped 4-byte alignment predicate at RV64: HOL `aligned 2 w`, i.e.
`w2n w MOD 2^2 = 0`. -/
def holAligned32_64 (address : RiscV.Word 64) : Bool :=
  address.toNat % 4 = 0

/-- HOL-shaped little/big-endian byte combination corresponding to
`word_of_bytes` over the four bytes of a 32-bit read, widened back to the word
carrier. -/
def holWordOfBytes64 (bigEndian : Bool) (bytes : List (RiscV.Word 64)) :
    RiscV.Word 64 :=
  let byte0 := bytes[0]?.getD 0
  let byte1 := bytes[1]?.getD 0
  let byte2 := bytes[2]?.getD 0
  let byte3 := bytes[3]?.getD 0
  if bigEndian then
    BitVec.ofNat 64
      (byte3.toNat + 256 * byte2.toNat + 256 ^ 2 * byte1.toNat +
        256 ^ 3 * byte0.toNat)
  else
    BitVec.ofNat 64
      (byte0.toNat + 256 * byte1.toNat + 256 ^ 2 * byte2.toNat +
        256 ^ 3 * byte3.toNat)

/-- HOL-shaped `mem_load_32` at RV64: alignment guard, aligned cell lookup,
domain guard, four byte reads and the endian word combination. -/
def holMemLoad32_64 (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (bigEndian : Bool)
    (address : RiscV.Word 64) : Option (RiscV.Word 64) :=
  if holAligned32_64 address then
    let aligned := holByteAlign64 address
    match memory aligned with
    | some value =>
        if domain aligned then
          some (holWordOfBytes64 bigEndian
            [holGetByte64 address value bigEndian,
             holGetByte64 (address + 1) value bigEndian,
             holGetByte64 (address + 2) value bigEndian,
             holGetByte64 (address + 3) value bigEndian])
        else none
    | none => none
  else none

theorem panRiscVAligned32_eq_holAligned32 (address : RiscV.Word 64) :
    RiscV.aligned address 4 = holAligned32_64 address := by
  simp [RiscV.aligned, holAligned32_64]

theorem holWordOfBytes64_eq_panRiscVWordOfBytes (bigEndian : Bool)
    (bytes : List (RiscV.Word 64)) :
    holWordOfBytes64 bigEndian bytes =
      RiscV.panRiscVWordOfBytes bigEndian bytes := by
  unfold holWordOfBytes64 RiscV.panRiscVWordOfBytes
  cases bytes with
  | nil => rfl
  | cons b0 rest =>
      cases rest with
      | nil => rfl
      | cons b1 rest =>
          cases rest with
          | nil => rfl
          | cons b2 rest =>
              cases rest with
              | nil => rfl
              | cons b3 rest => rfl

/-- The RISC-V model `panRiscVRead32` at the fixed 8-byte width equals the
HOL-shaped `mem_load_32` primitive over the memory view. -/
theorem panRiscVRead32_eight_eq_holMemLoad32_64
    (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (address : RiscV.Word 64) :
    RiscV.panRiscVRead32 domain memory (8 : RiscV.Word 64) address =
      holMemLoad32_64 domain memory false address := by
  simp only [RiscV.panRiscVRead32, panModelRead32, RiscV.panRiscVMemoryModel,
    panRiscVAligned32_eq_holAligned32, panRiscVByteAlign_eight_eq_holByteAlign64,
    holMemLoad32_64, holWordOfBytes64_eq_panRiscVWordOfBytes,
    panRiscVGetByte_eight_eq_holGetByte64]
  by_cases ha : holAligned32_64 address = true <;>
    cases hm : memory (holByteAlign64 address) <;>
    by_cases hd : domain (holByteAlign64 address) = true <;>
    simp_all

/-- The production `Load32` at the RV64 target equals HOL `mem_load_32` over
the memory view.  This is the genuine evaluator-case bridge for the `Load32`
constructor with a constant address. -/
theorem crepRuntimeLoad32_rv64_eq_holMemLoad32_64
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoad32 (riscv64CrepRuntimeTarget base) address =
      holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false
        address := by
  rw [crepRuntimeLoad32_target_eq_riscv, panRiscVRead32_eight_eq_holMemLoad32_64]

/-- Evaluator case: `evalCrepRuntimeExp` of `Load32 (Const address)` at the
RV64 target is exactly HOL `mem_load_32`. -/
theorem evalCrepRuntimeExp_load32_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load32 (.const address)) =
      holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false
        address := by
  simp [evalCrepRuntimeExp, crepRuntimeLoad32_rv64_eq_holMemLoad32_64]

/-- Word_lab evaluator case: the production word_lab core's `Load32 (Const
address)` at the RV64 target is HOL `mem_load_32` wrapped in `PanWordLab.word`. -/
theorem evalCrepRuntimeExpWordLab_load32_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base) (.load32 (.const address)) =
      (holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false
        address).map PanWordLab.word := by
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    crepRuntimeLoad32_rv64_eq_holMemLoad32_64]

/-- HOL-shaped word-cell load primitive for the RV64 target, mirroring
`crepSem$mem_load_def` (`if addr IN s.memaddrs then SOME (s.memory addr) else
NONE`) over a total `word -> word_lab`-viewed memory.  Flapjack-only adapter;
untagged pending full statement-shape review. -/
def holMemLoad64 (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (address : RiscV.Word 64) :
    Option (RiscV.Word 64) :=
  if domain address then memory address else none

/-- The RISC-V word-cell read primitive is exactly the HOL `mem_load` shape. -/
theorem panRiscVReadWord_eight_eq_holMemLoad64
    (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : PanFlatMemory (RiscV.Word 64)) (address : RiscV.Word 64) :
    RiscV.panRiscVReadWord domain memory address = holMemLoad64 domain memory address := rfl

/-- Production `crepRuntimeLoad` at the RV64 target equals the HOL-shaped
`mem_load` primitive over the total memory view. -/
theorem crepRuntimeLoad_rv64_eq_holMemLoad64
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    crepRuntimeLoad (riscv64CrepRuntimeTarget base) address =
      holMemLoad64 base.memaddrs (crepRuntimeMemoryView base.memory) address := by
  rw [crepRuntimeLoad_target_eq_riscv, panRiscVReadWord_eight_eq_holMemLoad64]

/-- Plain evaluator case: the production evaluator's `Load (Const address)` at
the RV64 target is the HOL-shaped `mem_load` primitive. -/
theorem evalCrepRuntimeExp_load_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load (.const address)) =
      holMemLoad64 base.memaddrs (crepRuntimeMemoryView base.memory) address := by
  simp [evalCrepRuntimeExp, crepRuntimeLoad_rv64_eq_holMemLoad64]

/-- Word_lab evaluator case: the production word_lab core's `Load (Const
address)` at the RV64 target is HOL `mem_load` wrapped in `PanWordLab.word`. -/
theorem evalCrepRuntimeExpWordLab_load_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base) (.load (.const address)) =
      (holMemLoad64 base.memaddrs (crepRuntimeMemoryView base.memory) address).map
        PanWordLab.word := by
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    crepRuntimeLoad_rv64_eq_holMemLoad64]

/-! ## The RV64 `Shift` evaluator case

HOL `crepSem$eval` evaluates `Shift sh e1 e2` by evaluating both operands and
then applying `word_sh sh w1 (w2n w2)` (`cakeml/pancake/semantics/crepSemScript.sml:131-133`).
`word_sh` (`cakeml/compiler/backend/wordLangScript.sml:313-321`) rejects an
amount that is nonzero and at least the word width, keeps amount zero, and
selects `Lsl`/`Lsr`/`Asr`/`Ror`.  The constant-operand case below is exactly
that primitive over the RV64 target.  Declaration notes: Flapjack-specific
bridge, intentionally untagged while the arbitrary runtime `memoryModel` hook
is only definitionally the fixed HOL primitive at this instantiation. -/

/-- The RV64 instance of HOL `word_sh`: amount zero is valid, a nonzero amount
at least the word width is invalid. -/
def holWordShift64 (operator : Shift) (value : RiscV.Word 64) (amount : Nat) :
    Option (RiscV.Word 64) :=
  if amount ≠ 0 ∧ 64 ≤ amount then none
  else
    match operator with
    | .lsl => some (value <<< amount)
    | .lsr => some (value >>> amount)
    | .asr => some (BitVec.sshiftRight value amount)
    | .ror => some (BitVec.rotateRight value amount)

theorem panRiscVShift_eight_eq_holWordShift64
    (operator : Shift) (left right : RiscV.Word 64) :
    RiscV.panRiscVShift operator left right =
      holWordShift64 operator left right.toNat := by
  unfold RiscV.panRiscVShift holWordShift64
  by_cases h : right.toNat < 64
  · have hnot : ¬ (right.toNat ≠ 0 ∧ 64 ≤ right.toNat) := by omega
    simp only [h, if_true, hnot, if_false]
    rfl
  · have hge : 64 ≤ right.toNat := by omega
    have hnz : right.toNat ≠ 0 := by omega
    simp [h, hnz, hge]

theorem crepRuntimeShift_rv64_eq_holWordShift64
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Shift) (left right : RiscV.Word 64) :
    (riscv64CrepRuntimeTarget base).memoryModel.shift operator left right =
      holWordShift64 operator left right.toNat := by
  change RiscV.panRiscVShift operator left right =
    holWordShift64 operator left right.toNat
  exact panRiscVShift_eight_eq_holWordShift64 operator left right

/-- Evaluator case: the production `Shift` over two constant operands at the
RV64 target is HOL `word_sh`. -/
theorem evalCrepRuntimeExp_shift_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Shift) (left right : RiscV.Word 64) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.shift operator (.const left) (.const right)) =
      holWordShift64 operator left right.toNat := by
  simp [evalCrepRuntimeExp, crepRuntimeShift_rv64_eq_holWordShift64]

/-- Word_lab evaluator case: the production word_lab core's `Shift` over two
constant operands at the RV64 target is HOL `word_sh` wrapped in
`PanWordLab.word`. -/
theorem evalCrepRuntimeExpWordLab_shift_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Shift) (left right : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base)
        (.shift operator (.const left) (.const right)) =
      (holWordShift64 operator left right.toNat).map PanWordLab.word := by
  simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp,
    crepRuntimeShift_rv64_eq_holWordShift64]

/-- Exact condition under which the production `Shift` hook coincides with
HOL's fixed `word_sh` at 64 bits.  `crepRuntimeShift_rv64_eq_holWordShift64`
is the `riscv64CrepRuntimeTarget` instance; an arbitrary `PanMemoryModel` need
not satisfy it, so this predicate names the precise assumption. -/
def CrepMemoryModelShiftMatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (operator : Shift) (left right : RiscV.Word 64),
    model.shift operator left right = holWordShift64 operator left right.toNat

/-- Source/production relation: any memory model satisfying
`CrepMemoryModelShiftMatchesHOL64` computes `Shift` as HOL `word_sh`. -/
theorem crepMemoryModelShift_eq_holWordShift64_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelShiftMatchesHOL64 model)
    (operator : Shift) (left right : RiscV.Word 64) :
    model.shift operator left right = holWordShift64 operator left right.toNat :=
  hmodel operator left right

/-- The RV64 target's memory model satisfies the shift/HOL-`word_sh` predicate. -/
theorem riscv64CrepRuntimeTarget_shift_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelShiftMatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun operator left right => crepRuntimeShift_rv64_eq_holWordShift64 base operator left right

/-- Generic production equation for `Shift` over *arbitrary* operand
expressions: the children are recursively evaluated and, whenever the model
satisfies the HOL-`word_sh` predicate, the hook is resolved as the HOL
primitive.  This composes the recursive evaluator; it is not a constant
specialization. -/
theorem evalCrepRuntimeExp_shift_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelShiftMatchesHOL64 base.memoryModel)
    (operator : Shift) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp base (.shift operator left right) =
      (evalCrepRuntimeExp base left).bind (fun leftWord =>
        (evalCrepRuntimeExp base right).bind (fun rightWord =>
          holWordShift64 operator leftWord rightWord.toNat)) := by
  simp only [CrepMemoryModelShiftMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExp, hmodel]
  rfl

/-- Word_lab version of `evalCrepRuntimeExp_shift_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_shift_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelShiftMatchesHOL64 base.memoryModel)
    (operator : Shift) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab base (.shift operator left right) =
      (evalCrepRuntimeExp base left).bind (fun leftWord =>
        (evalCrepRuntimeExp base right).bind (fun rightWord =>
          (holWordShift64 operator leftWord rightWord.toNat).map PanWordLab.word)) := by
  simp only [CrepMemoryModelShiftMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExpWordLab, hmodel]
  rfl

/-- Constant-operand specialization of `evalCrepRuntimeExp_shift_of_matches`. -/
theorem evalCrepRuntimeExp_shift_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelShiftMatchesHOL64 base.memoryModel)
    (operator : Shift) (left right : RiscV.Word 64) :
    evalCrepRuntimeExp base (.shift operator (.const left) (.const right)) =
      holWordShift64 operator left right.toNat := by
  simpa [evalCrepRuntimeExp] using
    evalCrepRuntimeExp_shift_of_matches base hmodel operator (.const left) (.const right)

/-- Constant-operand specialization of
`evalCrepRuntimeExpWordLab_shift_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_shift_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelShiftMatchesHOL64 base.memoryModel)
    (operator : Shift) (left right : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab base (.shift operator (.const left) (.const right)) =
      (holWordShift64 operator left right.toNat).map PanWordLab.word := by
  simpa [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp] using
    evalCrepRuntimeExpWordLab_shift_of_matches base hmodel operator (.const left) (.const right)

/-- Exact condition under which the production `Op` hook coincides with HOL's
fixed `word_op` at 64 bits.  `panRiscVWordOp_eq_wordOpHOL` is the
`riscv64CrepRuntimeTarget` instance; an arbitrary `PanMemoryModel` need not
satisfy it, so this predicate names the precise assumption. -/
def CrepMemoryModelOpMatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (operator : BinOp) (values : List (RiscV.Word 64)),
    model.wordOp operator values = wordOpHOL operator values

/-- Source/production relation: any memory model satisfying
`CrepMemoryModelOpMatchesHOL64` computes `Op` as HOL `word_op`. -/
theorem crepMemoryModelOp_eq_wordOpHOL_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelOpMatchesHOL64 model)
    (operator : BinOp) (values : List (RiscV.Word 64)) :
    model.wordOp operator values = wordOpHOL operator values :=
  hmodel operator values

/-- The RV64 target's memory model satisfies the `Op`/HOL-`word_op` predicate. -/
theorem riscv64CrepRuntimeTarget_op_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelOpMatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun operator values => panRiscVWordOp_eq_wordOpHOL operator values

/-- Generic production equation for `Op` over *arbitrary* operand
expressions: the children are recursively evaluated and, whenever the model
satisfies the HOL-`word_op` predicate, the hook is resolved as the HOL
primitive. -/
theorem evalCrepRuntimeExp_op_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelOpMatchesHOL64 base.memoryModel)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word 64))) :
    evalCrepRuntimeExp base (.op operator expressions) =
      (expressions.mapM (evalCrepRuntimeExp base)).bind
        (fun values => wordOpHOL operator values) := by
  simp only [CrepMemoryModelOpMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExp, hmodel]
  rfl

/-- Word_lab version of `evalCrepRuntimeExp_op_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_op_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelOpMatchesHOL64 base.memoryModel)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word 64))) :
    evalCrepRuntimeExpWordLab base (.op operator expressions) =
      (expressions.mapM (evalCrepRuntimeExp base)).bind
        (fun values => (wordOpHOL operator values).map PanWordLab.word) := by
  simp only [CrepMemoryModelOpMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExpWordLab, hmodel]
  rfl

/-- Constant-operand specialization of `evalCrepRuntimeExp_op_of_matches`. -/
theorem evalCrepRuntimeExp_op_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelOpMatchesHOL64 base.memoryModel)
    (operator : BinOp) (values : List (RiscV.Word 64)) :
    evalCrepRuntimeExp base (.op operator (values.map CrepExp.const)) =
      wordOpHOL operator values := by
  have hmapConst : List.mapM (evalCrepRuntimeExp base) (values.map CrepExp.const) = some values := by
    induction values with
    | nil => rfl
    | cons value rest ih =>
        simp [List.map_cons, List.mapM_cons, evalCrepRuntimeExp, ih]
  rw [evalCrepRuntimeExp_op_of_matches base hmodel operator (values.map CrepExp.const), hmapConst]
  rfl

/-- Constant-operand specialization of
`evalCrepRuntimeExpWordLab_op_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_op_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelOpMatchesHOL64 base.memoryModel)
    (operator : BinOp) (values : List (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab base (.op operator (values.map CrepExp.const)) =
      (wordOpHOL operator values).map PanWordLab.word := by
  have hmapConst : List.mapM (evalCrepRuntimeExp base) (values.map CrepExp.const) = some values := by
    induction values with
    | nil => rfl
    | cons value rest ih =>
        simp [List.map_cons, List.mapM_cons, evalCrepRuntimeExp, ih]
  rw [evalCrepRuntimeExpWordLab_op_of_matches base hmodel operator (values.map CrepExp.const), hmapConst]
  rfl

/-- Source/production relation: the exact condition under which an arbitrary
`PanMemoryModel` `compare` hook coincides with HOL's fixed `word_cmp`. -/
def CrepMemoryModelCmpMatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (operator : Cmp) (left right : RiscV.Word 64),
    model.compare operator left right = evalPanCmp operator left right

/-- Source/production relation: any memory model satisfying
`CrepMemoryModelCmpMatchesHOL64` computes `Cmp` as HOL `word_cmp`. -/
theorem crepMemoryModelCmp_eq_evalPanCmp_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelCmpMatchesHOL64 model)
    (operator : Cmp) (left right : RiscV.Word 64) :
    model.compare operator left right = evalPanCmp operator left right :=
  hmodel operator left right

/-- The RV64 target's memory model satisfies the `Cmp`/HOL-`word_cmp` predicate. -/
theorem riscv64CrepRuntimeTarget_cmp_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelCmpMatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun operator left right => panRiscVCmp_eq_evalPanCmp operator left right

/-- Generic production equation for `Cmp` over *arbitrary* operand
expressions: the children are recursively evaluated and, whenever the model
satisfies the HOL-`word_cmp` predicate, the hook is resolved as the HOL
primitive. -/
theorem evalCrepRuntimeExp_cmp_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelCmpMatchesHOL64 base.memoryModel)
    (operator : Cmp) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp base (.cmp operator left right) =
      (evalCrepRuntimeExp base left).bind (fun leftWord =>
        (evalCrepRuntimeExp base right).bind (fun rightWord =>
          some (evalPanCmp operator leftWord rightWord))) := by
  simp only [CrepMemoryModelCmpMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExp, hmodel]
  rfl

/-- Word_lab version of `evalCrepRuntimeExp_cmp_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_cmp_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelCmpMatchesHOL64 base.memoryModel)
    (operator : Cmp) (left right : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab base (.cmp operator left right) =
      (evalCrepRuntimeExp base left).bind (fun leftWord =>
        (evalCrepRuntimeExp base right).bind (fun rightWord =>
          some (.word (evalPanCmp operator leftWord rightWord)))) := by
  simp only [CrepMemoryModelCmpMatchesHOL64] at hmodel
  simp only [evalCrepRuntimeExpWordLab, hmodel]
  rfl

/-- Constant-operand specialization of `evalCrepRuntimeExp_cmp_of_matches`. -/
theorem evalCrepRuntimeExp_cmp_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelCmpMatchesHOL64 base.memoryModel)
    (operator : Cmp) (left right : RiscV.Word 64) :
    evalCrepRuntimeExp base (.cmp operator (.const left) (.const right)) =
      some (evalPanCmp operator left right) := by
  rw [evalCrepRuntimeExp_cmp_of_matches base hmodel operator (.const left) (.const right)]
  simp [evalCrepRuntimeExp]

/-- Constant-operand specialization of
`evalCrepRuntimeExpWordLab_cmp_of_matches`. -/
theorem evalCrepRuntimeExpWordLab_cmp_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelCmpMatchesHOL64 base.memoryModel)
    (operator : Cmp) (left right : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab base (.cmp operator (.const left) (.const right)) =
      some (.word (evalPanCmp operator left right)) := by
  rw [evalCrepRuntimeExpWordLab_cmp_of_matches base hmodel operator (.const left) (.const right)]
  simp [evalCrepRuntimeExp]

/-- HOL `byte$byte_align`/`byte$get_byte` hooks at 64 bits: a `PanMemoryModel`
whose 8-byte alignment and little-endian byte extraction agree with HOL.  This
is the exact condition under which an arbitrary `LoadByte` model coincides with
HOL `panSem$mem_load_byte`. -/
def CrepMemoryModelLoadByteMatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (address value : RiscV.Word 64),
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address ∧
    model.getByte (8 : RiscV.Word 64) address value false = holGetByte64 address value false

theorem crepMemoryModelLoadByte_align_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 model)
    (address value : RiscV.Word 64) :
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address :=
  (hmodel address value).1

theorem crepMemoryModelLoadByte_getByte_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 model)
    (address value : RiscV.Word 64) :
    model.getByte (8 : RiscV.Word 64) address value false =
      holGetByte64 address value false :=
  (hmodel address value).2

theorem riscv64CrepRuntimeTarget_loadByte_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelLoadByteMatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun address value =>
    ⟨panRiscVByteAlign_eight_eq_holByteAlign64 address,
      panRiscVGetByte_eight_eq_holGetByte64 address value⟩

/-- For any model matching the HOL byte hooks, and a state with an 8-byte
little-endian word, the production `LoadByte` is HOL `mem_load_byte`. -/
theorem crepRuntimeLoadByte_eq_holMemLoadByte64_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false)
    (address : RiscV.Word 64) :
    crepRuntimeLoadByte base address =
      holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  have halb := crepMemoryModelLoadByte_align_of_matches hmodel address 0
  simp only [crepRuntimeLoadByte, holMemLoadByte64, crepRuntimeMemoryView, hbytes, hbig]
  rw [halb]
  by_cases hd : base.memaddrs (holByteAlign64 address) = true
  · have hget := crepMemoryModelLoadByte_getByte_of_matches hmodel address
        (panTheWord (base.memory (holByteAlign64 address)))
    simp only [hd, hget, Option.pure_def]
  · simp [hd]

/-- Generic evaluator equation for `LoadByte` with an arbitrary address
expression, over any model matching the HOL byte hooks. -/
theorem evalCrepRuntimeExp_loadByte_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false)
    (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp base (.loadByte address) =
      (evalCrepRuntimeExp base address).bind (fun addressWord =>
        holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false addressWord) := by
  simp only [evalCrepRuntimeExp,
    crepRuntimeLoadByte_eq_holMemLoadByte64_of_matches base hmodel hbytes hbig]
  rfl

theorem evalCrepRuntimeExpWordLab_loadByte_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false)
    (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab base (.loadByte address) =
      (evalCrepRuntimeExp base address).bind (fun addressWord =>
        (holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false
          addressWord).map PanWordLab.word) := by
  simp only [evalCrepRuntimeExpWordLab,
    crepRuntimeLoadByte_eq_holMemLoadByte64_of_matches base hmodel hbytes hbig]
  rfl

theorem evalCrepRuntimeExp_loadByte_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false)
    (address : RiscV.Word 64) :
    evalCrepRuntimeExp base (.loadByte (.const address)) =
      holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  rw [evalCrepRuntimeExp_loadByte_of_matches base hmodel hbytes hbig (.const address)]
  simp [evalCrepRuntimeExp]

theorem evalCrepRuntimeExpWordLab_loadByte_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoadByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false)
    (address : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab base (.loadByte (.const address)) =
      (holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false address).map
        PanWordLab.word := by
  rw [evalCrepRuntimeExpWordLab_loadByte_of_matches base hmodel hbytes hbig (.const address)]
  simp [evalCrepRuntimeExp]

/-- The plain `Load` constructor uses only the `memaddrs` guard and the memory
cells, with no memory-model hook, so its arbitrary-address evaluator equation
holds for every RV64 runtime state. -/
theorem evalCrepRuntimeExp_load_rv64
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (fun addressWord => holMemLoad64 base.memaddrs
          (crepRuntimeMemoryView base.memory) addressWord) := by
  simp only [evalCrepRuntimeExp, crepRuntimeLoad_rv64_eq_holMemLoad64]
  rfl

/-- Word_lab version of the arbitrary-address plain `Load` equation. -/
theorem evalCrepRuntimeExpWordLab_load_rv64
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base) (.load address) =
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address).bind
        (fun addressWord => (holMemLoad64 base.memaddrs
          (crepRuntimeMemoryView base.memory) addressWord).map PanWordLab.word) := by
  simp only [evalCrepRuntimeExpWordLab, crepRuntimeLoad_rv64_eq_holMemLoad64]
  rfl

/-- The exact hook-matching condition under which an arbitrary `PanMemoryModel`
at RV64 reproduces HOL `mem_load_32`: alignment, byte alignment, byte reads, and
the four-byte endian combination all coincide with the HOL primitives. -/
def CrepMemoryModelLoad32MatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (address value : RiscV.Word 64),
    model.aligned 4 address = holAligned32_64 address ∧
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address ∧
    (∀ (byteAddress : RiscV.Word 64),
      model.getByte (8 : RiscV.Word 64) byteAddress value false =
        holGetByte64 byteAddress value false) ∧
    model.wordOfBytes false
        [holGetByte64 address value false, holGetByte64 (address + 1) value false,
         holGetByte64 (address + 2) value false, holGetByte64 (address + 3) value false] =
      holWordOfBytes64 false
        [holGetByte64 address value false, holGetByte64 (address + 1) value false,
         holGetByte64 (address + 2) value false, holGetByte64 (address + 3) value false]

theorem crepMemoryModelLoad32_aligned_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 model)
    (address value : RiscV.Word 64) :
    model.aligned 4 address = holAligned32_64 address := (hmodel address value).1

theorem crepMemoryModelLoad32_byteAlign_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 model)
    (address value : RiscV.Word 64) :
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address :=
  (hmodel address value).2.1

theorem crepMemoryModelLoad32_getByte_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 model)
    (address value : RiscV.Word 64) :
    ∀ (byteAddress : RiscV.Word 64),
      model.getByte (8 : RiscV.Word 64) byteAddress value false =
        holGetByte64 byteAddress value false :=
  (hmodel address value).2.2.1

theorem crepMemoryModelLoad32_wordOfBytes_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 model)
    (address value : RiscV.Word 64) :
    model.wordOfBytes false
        [holGetByte64 address value false, holGetByte64 (address + 1) value false,
         holGetByte64 (address + 2) value false, holGetByte64 (address + 3) value false] =
      holWordOfBytes64 false
        [holGetByte64 address value false, holGetByte64 (address + 1) value false,
         holGetByte64 (address + 2) value false, holGetByte64 (address + 3) value false] :=
  (hmodel address value).2.2.2

theorem riscv64CrepRuntimeTarget_load32_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelLoad32MatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun address value =>
    ⟨panRiscVAligned32_eq_holAligned32 address,
      panRiscVByteAlign_eight_eq_holByteAlign64 address,
      fun byteAddress => panRiscVGetByte_eight_eq_holGetByte64 byteAddress value,
      (holWordOfBytes64_eq_panRiscVWordOfBytes false _).symm⟩

theorem crepRuntimeLoad32_eq_holMemLoad32_64_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address : RiscV.Word 64) :
    crepRuntimeLoad32 base address =
      holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  have haligned := crepMemoryModelLoad32_aligned_of_matches hmodel address 0
  have hbyteAlign := crepMemoryModelLoad32_byteAlign_of_matches hmodel address 0
  have hgetByte := crepMemoryModelLoad32_getByte_of_matches hmodel address
    (panTheWord (base.memory (holByteAlign64 address)))
  have hwordOfBytes := crepMemoryModelLoad32_wordOfBytes_of_matches hmodel address
    (panTheWord (base.memory (holByteAlign64 address)))
  have h2 : (address + 1 + 1 : RiscV.Word 64) = address + 2 := by
    rw [BitVec.add_assoc, show (1 + 1 : RiscV.Word 64) = 2 from by decide]
  have h3 : (address + 1 + 1 + 1 : RiscV.Word 64) = address + 3 := by
    rw [BitVec.add_assoc, show (1 + 1 : RiscV.Word 64) = 2 from by decide, BitVec.add_assoc,
      show (1 + 2 : RiscV.Word 64) = 3 from by decide]
  simp only [crepRuntimeLoad32, holMemLoad32_64, crepRuntimeMemoryView, hbytes, hbig]
  rw [haligned, hbyteAlign]
  by_cases ha : holAligned32_64 address = true
  · simp only [ha, if_true]
    by_cases hd : base.memaddrs (holByteAlign64 address) = true
    · simp only [hd, if_true]
      rw [hgetByte address, hgetByte (address + 1), hgetByte (address + 1 + 1),
        hgetByte (address + 1 + 1 + 1), h3, h2, hwordOfBytes]
      simp only [Option.pure_def]
    · simp [hd]
  · simp [ha]

/-- Arbitrary-address `Load32` equation for any hook-matching model: the address
child is evaluated recursively, then HOL `mem_load_32` is applied. -/
theorem evalCrepRuntimeExp_load32_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExp base (.load32 address) =
      (evalCrepRuntimeExp base address).bind (fun addressWord =>
        holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false addressWord) := by
  simp only [evalCrepRuntimeExp,
    crepRuntimeLoad32_eq_holMemLoad32_64_of_matches base hmodel hbytes hbig]
  rfl

/-- Word_lab version of the arbitrary-address `Load32` equation. -/
theorem evalCrepRuntimeExpWordLab_load32_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address : CrepExp (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab base (.load32 address) =
      (evalCrepRuntimeExp base address).bind (fun addressWord =>
        (holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false
          addressWord).map PanWordLab.word) := by
  simp only [evalCrepRuntimeExpWordLab,
    crepRuntimeLoad32_eq_holMemLoad32_64_of_matches base hmodel hbytes hbig]
  rfl

/-- Constant-address corollary of the arbitrary-address `Load32` equation. -/
theorem evalCrepRuntimeExp_load32_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address : RiscV.Word 64) :
    evalCrepRuntimeExp base (.load32 (.const address)) =
      holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false address := by
  rw [evalCrepRuntimeExp_load32_of_matches base hmodel hbytes hbig (.const address)]
  simp [evalCrepRuntimeExp]

/-- Word_lab constant-address corollary of the arbitrary-address `Load32` equation. -/
theorem evalCrepRuntimeExpWordLab_load32_const_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelLoad32MatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address : RiscV.Word 64) :
    evalCrepRuntimeExpWordLab base (.load32 (.const address)) =
      (holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false address).map
        PanWordLab.word := by
  rw [evalCrepRuntimeExpWordLab_load32_of_matches base hmodel hbytes hbig (.const address)]
  simp [evalCrepRuntimeExp]

/-! ### Store family hook relations

HOL `panSemScript.sml` `mem_store_def` inserts a word directly, while
`mem_store_byte_def`/`mem_store_32_def` read the cell, replace a byte with
`set_byte`, and write the cell back.  The production store hooks are
`PanMemoryModel.byteAlign`/`setByte`; the predicates below name exactly when an
arbitrary runtime model coincides with the HOL fixed primitives. -/

/-- HOL `set_byte_def` at the fixed 8-byte width, with the byte index measured
in bytes (HOL reverses it for big endian). -/
def holSetByte64 (address byteValue cell : RiscV.Word 64) (bigEndian : Bool) : RiscV.Word 64 :=
  let byteCount := 8
  let byteIndex := if bigEndian then byteCount - 1 - address.toNat % byteCount
    else address.toNat % byteCount
  let offset := 256 ^ byteIndex
  let block := offset * 256
  let low := cell.toNat % offset
  let high := cell.toNat / block
  BitVec.ofNat 64 (low + (byteValue.toNat % 256) * offset + high * block)

theorem panRiscVSetByte_eight_eq_holSetByte64 (address byteValue cell : RiscV.Word 64) :
    RiscV.panRiscVSetByte (8 : RiscV.Word 64) address byteValue cell =
      holSetByte64 address byteValue cell false := by
  simp only [RiscV.panRiscVSetByte, panRiscVByteIndex_eight, holSetByte64, Bool.false_eq_true,
    if_false]

/-- HOL `panSemScript.sml` `mem_store_def`: guarded insertion of a word-labelled
value into the total memory function. -/
def holMemStore64 (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (address value : RiscV.Word 64) :
    Option (RiscV.Word 64 → PanWordLab (RiscV.Word 64)) :=
  if domain address then some (updateCrepRuntimeMemory memory address (.word value)) else none

/-- HOL `panSemScript.sml` `mem_store_byte_def`: guarded byte replacement in the
aligned cell of the total memory function. -/
def holMemStoreByte64 (domain : PanMemoryDomain (RiscV.Word 64))
    (memory : RiscV.Word 64 → PanWordLab (RiscV.Word 64))
    (bigEndian : Bool) (address byteValue : RiscV.Word 64) :
    Option (RiscV.Word 64 → PanWordLab (RiscV.Word 64)) :=
  let alignedAddress := holByteAlign64 address
  if domain alignedAddress then
    some (updateCrepRuntimeMemory memory alignedAddress
      (.word (holSetByte64 address byteValue (panTheWord (memory alignedAddress)) bigEndian)))
  else none

def CrepMemoryModelStoreByteMatchesHOL64 (model : PanMemoryModel (RiscV.Word 64)) : Prop :=
  ∀ (address byteValue cell : RiscV.Word 64),
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address ∧
    model.setByte (8 : RiscV.Word 64) address byteValue cell false =
      holSetByte64 address byteValue cell false

theorem crepMemoryModelStoreByte_align_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelStoreByteMatchesHOL64 model)
    (address byteValue cell : RiscV.Word 64) :
    model.byteAlign (8 : RiscV.Word 64) address = holByteAlign64 address :=
  (hmodel address byteValue cell).1

theorem crepMemoryModelStoreByte_setByte_of_matches
    {model : PanMemoryModel (RiscV.Word 64)}
    (hmodel : CrepMemoryModelStoreByteMatchesHOL64 model)
    (address byteValue cell : RiscV.Word 64) :
    model.setByte (8 : RiscV.Word 64) address byteValue cell false =
      holSetByte64 address byteValue cell false :=
  (hmodel address byteValue cell).2

theorem riscv64CrepRuntimeTarget_storeByte_matches_HOL64
    (base : CrepRuntimeState (RiscV.Word 64) σ) :
    CrepMemoryModelStoreByteMatchesHOL64 (riscv64CrepRuntimeTarget base).memoryModel :=
  fun address byteValue cell =>
    ⟨panRiscVByteAlign_eight_eq_holByteAlign64 address,
      panRiscVSetByte_eight_eq_holSetByte64 address byteValue cell⟩

/-- The production word store at the RV64 target is HOL `mem_store`: the memory
function is updated at the guarded address.  No memory-model hook is involved. -/
theorem crepRuntimeStore_rv64_eq_holMemStore64
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    crepRuntimeStore (riscv64CrepRuntimeTarget base) address value =
      (holMemStore64 base.memaddrs base.memory address value).map
        (fun memory => { riscv64CrepRuntimeTarget base with memory := memory }) := by
  simp only [crepRuntimeStore, holMemStore64, riscv64CrepRuntimeTarget]
  by_cases h : base.memaddrs address = true
  · simp only [h, if_true, Option.map_some]
  · simp [h]

/-- The production byte store is HOL `mem_store_byte` under the `setByte`
matching predicate. -/
theorem crepRuntimeStoreByte_eq_holMemStoreByte64_of_matches
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (hmodel : CrepMemoryModelStoreByteMatchesHOL64 base.memoryModel)
    (hbytes : base.bytesInWord = (8 : RiscV.Word 64))
    (hbig : base.bigEndian = false) (address byteValue : RiscV.Word 64) :
    crepRuntimeStoreByte base address byteValue =
      (holMemStoreByte64 base.memaddrs base.memory false address byteValue).map
        (fun memory => { base with memory := memory }) := by
  have halign := crepMemoryModelStoreByte_align_of_matches hmodel address byteValue
    (panTheWord (base.memory (holByteAlign64 address)))
  have hset := crepMemoryModelStoreByte_setByte_of_matches hmodel address byteValue
    (panTheWord (base.memory (holByteAlign64 address)))
  simp only [crepRuntimeStoreByte, holMemStoreByte64, hbytes, hbig]
  rw [halign]
  by_cases hd : base.memaddrs (holByteAlign64 address) = true
  · simp only [hd, if_true]
    rw [hset]
    simp only [Option.pure_def, Option.map_some]
  · simp [hd]

/-- The production word store is HOL `mem_store` for any model: no memory-model
hook is involved. -/
theorem crepRuntimeStore_eq_holMemStore64
    (base : CrepRuntimeState (RiscV.Word 64) σ) (address value : RiscV.Word 64) :
    crepRuntimeStore base address value =
      (holMemStore64 base.memaddrs base.memory address value).map
        (fun memory => { base with memory := memory }) := by
  simp only [crepRuntimeStore, holMemStore64]
  by_cases h : base.memaddrs address = true
  · simp only [h, if_true, Option.map_some]
  · simp [h]

/-! HOL `crepSemScript.sml` `crep_op_def` shape at 64 bits: `Mul` over exactly
two word operands yields their product, any other arity is a failure. -/
def holCrepOpMul64 (values : List (RiscV.Word 64)) : Option (RiscV.Word 64) :=
  match values with
  | [left, right] => some (left * right)
  | _ => none

/-- Evaluator case: the production `Crepop Mul` over constant operands at the
RV64 target is HOL `crep_op`. -/
theorem evalCrepRuntimeExp_crepOpMul_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (args : List (RiscV.Word 64)) :
    evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.crepOp .mul (args.map (fun value => .const value))) =
      holCrepOpMul64 args := by
  cases args with
  | nil => simp [evalCrepRuntimeExp, holCrepOpMul64]
  | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp, holCrepOpMul64]
      | cons right tail =>
          cases tail with
          | nil => simp [evalCrepRuntimeExp, holCrepOpMul64]
          | cons extra more => simp [evalCrepRuntimeExp, holCrepOpMul64]

/-- Word_lab evaluator case: the production word_lab core's `Crepop Mul` over
constant operands at the RV64 target is HOL `crep_op` wrapped in
`PanWordLab.word`. -/
theorem evalCrepRuntimeExpWordLab_crepOpMul_rv64_const
    (base : CrepRuntimeState (RiscV.Word 64) σ)
    (args : List (RiscV.Word 64)) :
    evalCrepRuntimeExpWordLab (riscv64CrepRuntimeTarget base)
        (.crepOp .mul (args.map (fun value => .const value))) =
      (holCrepOpMul64 args).map PanWordLab.word := by
  cases args with
  | nil => simp [evalCrepRuntimeExpWordLab, holCrepOpMul64]
  | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExpWordLab, holCrepOpMul64]
      | cons right tail =>
          cases tail with
          | nil => simp [evalCrepRuntimeExpWordLab, evalCrepRuntimeExp, holCrepOpMul64]
          | cons extra more => simp [evalCrepRuntimeExpWordLab, holCrepOpMul64]

/- HOL-shaped total 64-bit reference evaluator over the production RV64 Crep
runtime state.  It uses the reviewed `holMemLoad*`/`holWordShift64`/`wordOpHOL`
primitives and HOL `crepSem$eval`'s recursive structure (children are re-evaluated
by the reference itself).  It is Flapjack-only adapter infrastructure, not a HOL
port: the production evaluator's `Op`/`Cmp`/`Shift`/byte-load arms still delegate
to the arbitrary runtime `memoryModel` hooks rather than HOL fixed primitives, so
no `@[hol]` tag is attached (tracked by bead flapjack-pxn.18.4.3.48.1). -/
mutual
  def holCrepEval64 (base : CrepRuntimeState (RiscV.Word 64) Unit) :
      CrepExp (RiscV.Word 64) → Option (PanWordLab (RiscV.Word 64))
    | .const value => some (.word value)
    | .var name => base.locals name
    | .loadGlob name => base.globals name
    | .load address => do
        let cell ← holCrepEval64 base address
        let .word word := cell
        (holMemLoad64 base.memaddrs (crepRuntimeMemoryView base.memory) word).map
          PanWordLab.word
    | .load32 address => do
        let cell ← holCrepEval64 base address
        let .word word := cell
        (holMemLoad32_64 base.memaddrs (crepRuntimeMemoryView base.memory) false
          word).map PanWordLab.word
    | .loadByte address => do
        let cell ← holCrepEval64 base address
        let .word word := cell
        (holMemLoadByte64 base.memaddrs (crepRuntimeMemoryView base.memory) false
          word).map PanWordLab.word
    | .op operator expressions => do
        let cells ← holCrepEvals64 base expressions
        let words ← cells.mapM (fun cell => (let .word word := cell; some word))
        (wordOpHOL operator words).map PanWordLab.word
    | .crepOp .mul [left, right] => do
        let leftCell ← holCrepEval64 base left
        let rightCell ← holCrepEval64 base right
        let .word leftWord := leftCell
        let .word rightWord := rightCell
        pure (.word (leftWord * rightWord))
    | .cmp operator left right => do
        let leftCell ← holCrepEval64 base left
        let rightCell ← holCrepEval64 base right
        let .word leftWord := leftCell
        let .word rightWord := rightCell
        pure (.word (RiscV.panRiscVCmp operator leftWord rightWord))
    | .shift operator left right => do
        let leftCell ← holCrepEval64 base left
        let rightCell ← holCrepEval64 base right
        let .word leftWord := leftCell
        let .word rightWord := rightCell
        (holWordShift64 operator leftWord rightWord.toNat).map PanWordLab.word
    | .baseAddr => some (.word base.baseAddress)
    | .topAddr => some (.word base.topAddress)
    | _ => none
  def holCrepEvals64 (base : CrepRuntimeState (RiscV.Word 64) Unit) :
      List (CrepExp (RiscV.Word 64)) → Option (List (PanWordLab (RiscV.Word 64)))
    | [] => some []
    | expression :: expressions => do
        let cell ← holCrepEval64 base expression
        let cells ← holCrepEvals64 base expressions
        pure (cell :: cells)
end

/-- The reference list evaluator is the `mapM` of the reference expression evaluator. -/
theorem holCrepEvals64_eq_mapM (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (expressions : List (CrepExp (RiscV.Word 64))) :
    holCrepEvals64 base expressions = expressions.mapM (holCrepEval64 base) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [holCrepEvals64, List.mapM_cons]
      cases h : holCrepEval64 base expression <;> simp [ih]

/-- Unwrapping a list of `word_lab` cells that were all built by `PanWordLab.word`
recovers the original bare words. -/
theorem mapM_unwrap_mapWord (values : List (RiscV.Word 64)) :
    (values.map PanWordLab.word).mapM
        (fun cell => (let .word word := cell; some word)) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.map_cons, List.mapM_cons, ih]

/-- The first-field projection of a `word_lab` cell list built by `PanWordLab.word`
recovers the original bare words. -/
theorem mapM_some_fst_map_word (values : List (RiscV.Word 64)) :
    (values.map PanWordLab.word).mapM (fun cell => some cell.1) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.map_cons, List.mapM_cons, ih]

/-- `mapM` of `some` is `some` of the list. -/
theorem list_mapM_some (values : List (RiscV.Word 64)) :
    values.mapM (fun value => some value) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ih]

/-- The production list evaluator is the `mapM` of the expression evaluator. -/
theorem evalCrepRuntimeExps_eq_mapM_of
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (expressions : List (CrepExp α)) :
    evalCrepRuntimeExps state expressions = expressions.mapM (evalCrepRuntimeExp state) := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps]
  | cons expression expressions ih =>
      simp only [evalCrepRuntimeExps, List.mapM_cons]
      cases h : evalCrepRuntimeExp state expression <;> simp [ih]

mutual
  /-- Production/bare RV64 Crep evaluator correspondence with the HOL-shaped
  reference evaluator, read back through `PanWordLab.word`.  Flapjack-only
  adapter theorem (no `@[hol]` tag): the production `Op`/`Cmp`/`Shift`/byte-load
  arms still go through the runtime `memoryModel` hooks, which the correspondence
  identifies with the reviewed HOL-shaped primitives only at this RV64 target. -/
  theorem evalCrepRuntimeExp_map_eq_holCrepEval64
      (base : CrepRuntimeState (RiscV.Word 64) Unit)
      (expression : CrepExp (RiscV.Word 64)) :
      (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) expression).map PanWordLab.word =
        holCrepEval64 base expression := by
    cases expression with
    | const value => simp [evalCrepRuntimeExp, holCrepEval64]
    | var name =>
        simp [evalCrepRuntimeExp, holCrepEval64, riscv64CrepRuntimeTarget,
          Function.comp_def, optionMapWordPanTheWord]
    | loadGlob name =>
        simp [evalCrepRuntimeExp, holCrepEval64, riscv64CrepRuntimeTarget,
          Function.comp_def, optionMapWordPanTheWord]
    | baseAddr => simp [evalCrepRuntimeExp, holCrepEval64, riscv64CrepRuntimeTarget]
    | topAddr => simp [evalCrepRuntimeExp, holCrepEval64, riscv64CrepRuntimeTarget]
    | load address =>
        cases h : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address with
        | none =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address]
        | some addressWord =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address,
              crepRuntimeLoad_rv64_eq_holMemLoad64]
    | load32 address =>
        cases h : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address with
        | none =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address]
        | some addressWord =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address,
              crepRuntimeLoad32_rv64_eq_holMemLoad32_64]
    | loadByte address =>
        cases h : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) address with
        | none =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address]
        | some addressWord =>
            simp [evalCrepRuntimeExp, holCrepEval64, h,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base address,
              crepRuntimeLoadByte_rv64_eq_holMemLoadByte64]
    | op operator expressions =>
        simp only [evalCrepRuntimeExp, holCrepEval64]
        rw [← evalCrepRuntimeExps_map_eq_holCrepEvals64 base expressions]
        rw [← evalCrepRuntimeExps_eq_mapM_of (riscv64CrepRuntimeTarget base) expressions]
        simp [Option.bind_map, Option.map_bind, Option.bind_some, Function.comp_def,
          list_mapM_some, riscv64CrepRuntimeTarget_memoryModel,
          RiscV.panRiscVMemoryModel, RiscV.panRiscVWordOp, wordOpHOL]
    | crepOp operator expressions =>
        cases operator
        cases expressions with
        | nil => simp [evalCrepRuntimeExp, holCrepEval64]
        | cons left rest =>
            cases rest with
            | nil => simp [evalCrepRuntimeExp, holCrepEval64]
            | cons right tail =>
                cases tail with
                | nil =>
                    cases hl : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) left with
                    | none =>
                        have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
                        rw [hl, Option.map_none] at ihl
                        simp [evalCrepRuntimeExp, holCrepEval64, hl, ← ihl]
                    | some leftWord =>
                        cases hr : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) right with
                        | none =>
                            have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
                            rw [hl, Option.map_some] at ihl
                            have ihr := evalCrepRuntimeExp_map_eq_holCrepEval64 base right
                            rw [hr, Option.map_none] at ihr
                            simp [evalCrepRuntimeExp, holCrepEval64, hl, hr, ← ihl, ← ihr]
                        | some rightWord =>
                            have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
                            rw [hl, Option.map_some] at ihl
                            have ihr := evalCrepRuntimeExp_map_eq_holCrepEval64 base right
                            rw [hr, Option.map_some] at ihr
                            simp [evalCrepRuntimeExp, holCrepEval64, hl, hr, ← ihl, ← ihr]
                | cons extra more => simp [evalCrepRuntimeExp, holCrepEval64]
    | cmp operator left right =>
        cases hl : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) left with
        | none =>
            have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
            rw [hl, Option.map_none] at ihl
            simp [evalCrepRuntimeExp, holCrepEval64, hl, ← ihl]
        | some leftWord =>
            cases hr : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) right with
            | none =>
                have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
                rw [hl, Option.map_some] at ihl
                have ihr := evalCrepRuntimeExp_map_eq_holCrepEval64 base right
                rw [hr, Option.map_none] at ihr
                simp [evalCrepRuntimeExp, holCrepEval64, hl, hr, ← ihl, ← ihr]
            | some rightWord =>
                have ihl := evalCrepRuntimeExp_map_eq_holCrepEval64 base left
                rw [hl, Option.map_some] at ihl
                have ihr := evalCrepRuntimeExp_map_eq_holCrepEval64 base right
                rw [hr, Option.map_some] at ihr
                simp [evalCrepRuntimeExp, holCrepEval64, hl, hr, ← ihl, ← ihr,
                  riscv64CrepRuntimeTarget_memoryModel, RiscV.panRiscVMemoryModel]
    | shift operator left right =>
        cases hl : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) left with
        | none =>
            simp [evalCrepRuntimeExp, holCrepEval64, hl,
              ← evalCrepRuntimeExp_map_eq_holCrepEval64 base left]
        | some leftWord =>
            cases hr : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) right with
            | none =>
                simp [evalCrepRuntimeExp, holCrepEval64, hl, hr,
                  ← evalCrepRuntimeExp_map_eq_holCrepEval64 base left,
                  ← evalCrepRuntimeExp_map_eq_holCrepEval64 base right]
            | some rightWord =>
                simp [evalCrepRuntimeExp, holCrepEval64, hl, hr,
                  ← evalCrepRuntimeExp_map_eq_holCrepEval64 base left,
                  ← evalCrepRuntimeExp_map_eq_holCrepEval64 base right,
                  crepRuntimeShift_rv64_eq_holWordShift64, Option.bind_some]

  /-- Production/bare RV64 Crep list-evaluator correspondence with the
  HOL-shaped reference list evaluator. -/
  theorem evalCrepRuntimeExps_map_eq_holCrepEvals64
      (base : CrepRuntimeState (RiscV.Word 64) Unit)
      (expressions : List (CrepExp (RiscV.Word 64))) :
      (evalCrepRuntimeExps (riscv64CrepRuntimeTarget base) expressions).map
          (List.map PanWordLab.word) =
        holCrepEvals64 base expressions := by
    cases expressions with
    | nil => simp [evalCrepRuntimeExps, holCrepEvals64]
    | cons expression expressions =>
        simp only [evalCrepRuntimeExps, holCrepEvals64]
        cases h : evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) expression with
        | none =>
            have he := evalCrepRuntimeExp_map_eq_holCrepEval64 base expression
            rw [h, Option.map_none] at he
            rw [← he]
            rfl
        | some value =>
            have he := evalCrepRuntimeExp_map_eq_holCrepEval64 base expression
            rw [h, Option.map_some] at he
            have ht := evalCrepRuntimeExps_map_eq_holCrepEvals64 base expressions
            rw [← he, ← ht]
            simp [Option.map_bind, Option.bind_map, Function.comp_def]
end

/-- Composition of the generic `Shift` equation with the all-expression
recursive bridge: for arbitrary (possibly nested) `Shift` expressions at the
RV64 target, whose model satisfies the HOL-`word_sh` predicate, production
evaluation maps onto the HOL-shaped `holCrepEval64`. -/
theorem evalCrepRuntimeExp_shift_map_eq_holCrepEval64
    (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (operator : Shift) (left right : CrepExp (RiscV.Word 64)) :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.shift operator left right)).map PanWordLab.word =
      holCrepEval64 base (.shift operator left right) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 base _

/-- Composition of the generic `Op` equation with the all-expression
recursive bridge: for arbitrary (possibly nested) `Op` expressions at the RV64
target, whose model satisfies the HOL-`word_op` predicate, production
evaluation maps onto the HOL-shaped `holCrepEval64`. -/
theorem evalCrepRuntimeExp_op_map_eq_holCrepEval64
    (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (operator : BinOp) (expressions : List (CrepExp (RiscV.Word 64))) :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.op operator expressions)).map PanWordLab.word =
      holCrepEval64 base (.op operator expressions) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 base _

/-- Composition of the generic `Cmp` equation with the all-expression
recursive bridge: for arbitrary (possibly nested) `Cmp` expressions at the RV64
target, whose model satisfies the HOL-`word_cmp` predicate, production
evaluation maps onto the HOL-shaped `holCrepEval64`. -/
theorem evalCrepRuntimeExp_cmp_map_eq_holCrepEval64
    (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (operator : Cmp) (left right : CrepExp (RiscV.Word 64)) :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base)
        (.cmp operator left right)).map PanWordLab.word =
      holCrepEval64 base (.cmp operator left right) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 base _

/-- Composition corollary: an arbitrary-address plain `Load` at the RV64 target
composes with the all-expression correspondence to `holCrepEval64`. -/
theorem evalCrepRuntimeExp_load_map_eq_holCrepEval64
    (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (address : CrepExp (RiscV.Word 64)) :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load address)).map
        PanWordLab.word =
      holCrepEval64 base (.load address) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 base _

/-- Composition corollary: an arbitrary-address `Load32` at the RV64 target
composes with the all-expression correspondence to `holCrepEval64`. -/
theorem evalCrepRuntimeExp_load32_map_eq_holCrepEval64
    (base : CrepRuntimeState (RiscV.Word 64) Unit)
    (address : CrepExp (RiscV.Word 64)) :
    (evalCrepRuntimeExp (riscv64CrepRuntimeTarget base) (.load32 address)).map
        PanWordLab.word =
      holCrepEval64 base (.load32 address) :=
  evalCrepRuntimeExp_map_eq_holCrepEval64 base _

end Flapjack
