import Flapjack.PanBst
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.RiscV.PanMemory

/-!
HOL-shaped expression evaluation inputs for a 64-bit Pancake state.

The source `panSem$eval` reads locals, globals, structs, memory, `memaddrs`,
`sh_memaddrs`, and `be` from its state.  The generic value evaluator takes
those memory inputs as explicit arguments, so this module derives them from
`PanSemState` and supplies the 64-bit word operations.  The result is an
untagged evaluator boundary; the generic HOL theorem remains untagged until
the full polymorphic `word` interface is represented in Lean.
-/

namespace Flapjack

/-- RISC-V 64-bit source word model with the full HOL `be` behavior. -/
def panSemBitVec64WordModel : PanMemoryModel (RiscV.Word 64) := by
  let model := RiscV.panRiscVMemoryModel (width := 64)
  exact { model with
    getByte := fun bytesInWord address value bigEndian =>
      let byteIndex := RiscV.panRiscVByteIndex bytesInWord address
      let byteIndex := if bigEndian then bytesInWord.toNat - byteIndex - 1
        else byteIndex
      BitVec.ofNat 64 ((value.toNat / 256 ^ byteIndex) % 256)
    setByte := fun bytesInWord address byte value bigEndian =>
      let byteIndex := RiscV.panRiscVByteIndex bytesInWord address
      let byteIndex := if bigEndian then bytesInWord.toNat - byteIndex - 1
        else byteIndex
      let offset := 256 ^ byteIndex
      let block := offset * 256
      let low := value.toNat % offset
      let high := value.toNat / block
      BitVec.ofNat 64 (low + (byte.toNat % 256) * offset + high * block) }

/-- Source word size for the fixed 64-bit specialization. -/
def panSemBitVec64BytesInWord : RiscV.Word 64 := 8

/-- Build the evaluator's ordinary/shared memory operations from the source
    state domains and endianness.  The source state owns these parameters; no
    independent domain or endian argument is accepted here. -/
def panSemBitVec64MemoryAccess (state : PanSemState (RiscV.Word 64) ffi) :
    PanValueMemoryAccess (RiscV.Word 64) :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel
    state.memaddrs state.sharedMemaddrs state.be

/-- Full state-owned source code-map evaluator for the RISC-V 64-bit word
    model. It derives the memory domains and endianness from the PanSem state
    and fixes the source width from the word type, without consulting a Crep
    runtime state. -/
def panSemEvaluateRiscV64CodeState [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)]
    [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (program : Prog (RiscV.Word 64)) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  panSemEvaluateCodeStateWithMemoryModel context primitive handler
    panSemBitVec64WordModel panSemBitVec64BytesInWord state program

/-- Evaluate one source expression using the word-memory inputs derived from
    its `PanSemState`. -/
def evalPanSemStateExp [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)] [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)] [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) ffi) (expression : Exp (RiscV.Word 64)) :
    Option (PanValue (RiscV.Word 64)) :=
  evalPanValueExp state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord expression
    (memoryAccess := some (panSemBitVec64MemoryAccess state))

/-- HOL's `OPT_MMAP (eval s)` sequence boundary over the state-derived
    evaluator. -/
def evalPanSemStateExps [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)] [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)] [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) ffi)
    (expressions : List (Exp (RiscV.Word 64))) :
    Option (List (PanValue (RiscV.Word 64))) :=
  evalPanValueExps state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord expressions
    (memoryAccess := some (panSemBitVec64MemoryAccess state))


/-- The executed 64-bit source `.op` branch consults exactly the tagged
`wordOpHOL` list fold. `panSemBitVec64MemoryAccess` is built from
`RiscV.panRiscVMemoryModel`, whose `wordOp` is `panRiscVWordOp = wordOpHOL`;
this is the arbitrary-operand-list delegation used by the exact-state path.
The generic `memoryAccess := none` compatibility branch remains untagged and
is tracked separately as a mismatch. -/
theorem panSemBitVec64MemoryAccess_wordOp
    (state : PanSemState (RiscV.Word 64) ffi) (operator : BinOp)
    (values : List (RiscV.Word 64)) :
    (panSemBitVec64MemoryAccess state).wordOp operator values =
      wordOpHOL operator values := rfl

/-- Unfolding of the executed source `.op` clause: for an arbitrary operand
list it evaluates the arguments and then applies the tagged `wordOpHOL`
fold. This pins the exact-state path to `wordOpHOL` without changing the
generic compatibility branch. -/
theorem evalPanSemStateExp_op
    (state : PanSemState (RiscV.Word 64) ffi) (operator : BinOp)
    (arguments : List (Exp (RiscV.Word 64))) :
    evalPanSemStateExp state (.op operator arguments) =
      (evalPanSemStateExps state arguments).bind (fun values =>
        (values.mapM panValueWordProjection).bind (fun words =>
          (wordOpHOL operator words).map PanValue.word)) := by
  simp only [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp.eq_def,
    panSemBitVec64MemoryAccess_wordOp]
  rfl

/-- HOL `byte_align` (`cakeml/.../alignmentScript.sml`): clear the low
    `LOG2 (dimindex DIV 8)` bits.  This is NOT division by `width / 8`; they agree
    only when `width / 8` is a power of two (e.g. width 64), so the tagged
    `mem_load_byte_def`/`mem_load_32_def` ports use this exact alignment.  HOL's
    alignment lives in the standard library, outside the CakeML submodule, so
    this helper is untagged. -/
def panByteAlignHOL {width : Nat} (address : RiscV.Word width) : RiscV.Word width :=
  let bits := Nat.log2 (width / 8)
  (address >>> bits) <<< bits

/-- Exact port of HOL `mem_load_byte_def` (`panSemScript.sml:86`) over the
faithful source memory shape: `m` is a total `'a word → 'a word_lab` map
(here `HolWordLab`), `dm` is a word set rendered as a `Prop` predicate, and
the result is the exact `word8` option.  The executed
`PanValueMemoryAccess.readByte` widens the decoded byte to the word carrier;
that widening is the separate production adapter, tracked by
flapjack-pxn.18.3.6.9.2. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_byte_def"]
def panMemLoadByteHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option UInt8 :=
  let aligned := panByteAlignHOL (width := width) address
  match memory aligned with
  | .word value =>
      if domain aligned then
        some (UInt8.ofNat
          (RiscV.panRiscVGetByteEndian (BitVec.ofNat width (width / 8)) address
            value bigEndian).toNat)
      else none

/-- Exact port of HOL `mem_load_32_def`
    (`cakeml/pancake/semantics/panSemScript.sml:94-104`).  When `aligned 2` holds
    at the address, the four consecutive bytes `w`, `w+1`, `w+2`, `w+3` of the
    stored word are reassembled (in the requested byte order) into a `word32`;
    out-of-domain or unaligned addresses yield `NONE`.  As in
    `panMemLoadByteHOL`, HOL's total `word_lab` memory is rendered as a total
    map into `HolWordLab` and the `word set` domain as a `Prop` predicate. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_32_def"]
def panMemLoad32HOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option (RiscV.Word 32) :=
  if (address >>> 2) <<< 2 = address then
    let aligned := panByteAlignHOL (width := width) address
    match memory aligned with
    | .word value =>
        if domain aligned then
          let getByte := RiscV.panRiscVGetByteEndian
            (BitVec.ofNat width (width / 8))
          let bytes :=
            [ getByte address value bigEndian,
              getByte (address + 1) value bigEndian,
              getByte (address + 2) value bigEndian,
              getByte (address + 3) value bigEndian ]
          some (RiscV.panRiscVWordOfBytes (width := 32) bigEndian
            (bytes.map (fun byte => BitVec.ofNat 32 byte.toNat)))
        else none
  else none


/-- HOL `size_of_sh_with_ctxt` (`cakeml/pancake/panLangScript.sml:164-171`), the
    context-sensitive shape size used by `mem_load` to advance the address. -/
def sizeOfShWithCtxt (context : StructContextHOL) : Shape → Nat
  | .one => 1
  | .comb shapes => shapes.foldl (fun total shape => total + sizeOfShWithCtxt context shape) 0
  | .named name =>
      match lookupInfo name context with
      | some info => info.size
      | none => 1
termination_by shape => sizeOf shape
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial


/-- HOL `bytes_in_word` (`n2w (dimindex(:'a) DIV 8)`), used by `mem_load` to
    advance the address between structure fields. -/
def panBytesInWord (width : Nat) : RiscV.Word width :=
  BitVec.ofNat width (width / 8)

/-! Statement-exact port of HOL `panSem$mem_load` (`cakeml/pancake/semantics/panSemScript.sml:137`,
    defining `mem_load`, `mem_loads`, and `mem_load_flds`).  The argument order
    follows HOL currying (`mem_load sh addr dm m stcs`), and `bytes_in_word` is
    the canonical `panBytesInWord width`, exactly as HOL's global
    `bytes_in_word = n2w (dimindex(:'a) DIV 8)` (no free parameter).  The struct
    context is the HOL-shaped `StructContextHOL`; the memory is rendered as a
    total `HolWordLab` map with a `Prop` domain (HOL `'a word set`).  HOL's
    `Named` lookup `dropWhile (\(n,i). ~(n = nm)) stcs` is inlined as the
    equivalent structural scan over the context (needed for the Lean termination
    measure `(structs.length, sizeOf shape)`, the image of HOL's lexicographic
    `(LENGTH stcs, shape_size)`); the scan returns the first name match together
    with the remaining context, exactly the `(nm,info)::stcs'` HOL destructures. -/
mutual
  @[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_def"]
  def panMemLoadHOL {width : Nat} (shape : Shape) (address : RiscV.Word width)
      (domain : RiscV.Word width → Prop) [DecidablePred domain]
      (memory : RiscV.Word width → HolWordLab width) (structs : StructContextHOL) :
      Option (HolValue width) :=
    match shape with
    | .one => if domain address then some (.val (memory address)) else none
    | .comb shapes =>
        match panMemLoadsHOL shapes address domain memory structs with
        | some values => some (.rStruct values)
        | none => none
    | .named name =>
        match structs with
        | [] => none
        | (candidate, info) :: rest =>
            if candidate == name then
              match panMemLoadFldsHOL info.fields address domain memory rest with
              | some fields => some (.nStruct candidate fields)
              | none => none
            else panMemLoadHOL (.named name) address domain memory rest
  termination_by (structs.length, sizeOf shape)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  def panMemLoadsHOL {width : Nat} (shapes : List Shape) (address : RiscV.Word width)
      (domain : RiscV.Word width → Prop) [DecidablePred domain]
      (memory : RiscV.Word width → HolWordLab width) (structs : StructContextHOL) :
      Option (List (HolValue width)) :=
    match shapes with
    | [] => some []
    | shape :: rest =>
        match panMemLoadHOL shape address domain memory structs,
              panMemLoadsHOL rest
                (address + panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt structs shape))
                domain memory structs with
        | some value, some values => some (value :: values)
        | _, _ => none
  termination_by (structs.length, sizeOf shapes)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  def panMemLoadFldsHOL {width : Nat} (fields : List (FieldName × Shape)) (address : RiscV.Word width)
      (domain : RiscV.Word width → Prop) [DecidablePred domain]
      (memory : RiscV.Word width → HolWordLab width) (structs : StructContextHOL) :
      Option (List (FieldName × HolValue width)) :=
    match fields with
    | [] => some []
    | (field, shape) :: rest =>
        match panMemLoadHOL shape address domain memory structs,
              panMemLoadFldsHOL rest
                (address + panBytesInWord width * BitVec.ofNat width (sizeOfShWithCtxt structs shape))
                domain memory structs with
        | some value, some values => some ((field, value) :: values)
        | _, _ => none
  termination_by (structs.length, sizeOf fields)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hpair
         have : sizeOf shape < sizeOf ((field, shape) : FieldName × Shape) := by simp +arith
         have := List.sizeOf_lt_of_mem hpair
         omega)
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)
end

/-! ## Executed-path widening adapter (flapjack-pxn.18.3.6.9.2)

The executed BitVec-64 memory access `readByte` (via `panSemBitVec64MemoryAccess`)
agrees with the tagged exact `panMemLoadByteHOL` when the faithful word memory is
derived from a `PanValue` memory.  These declarations are Flapjack-specific
production-side adapters (not HOL statements); the generic `memoryAccess := none`
compatibility branch remains untagged and mismatch-tracked. -/

/-- Word view of a `PanValue` memory: word cells are kept, non-word cells and
    absent addresses are read as the zero word (the `HolWordLab` total memory). -/
def panValueWordHOL (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) :
    RiscV.Word 64 → HolWordLab 64 :=
  fun address => match memory address with
    | some (.word value) => .word value
    | _ => .word 0

/-- Definedness of a `PanValue` memory cell as a word (the `Prop` domain's
    decidable Boolean guard). -/
def panValueWordDefined
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) :
    RiscV.Word 64 → Bool :=
  fun address => match memory address with
    | some (.word _) => true
    | _ => false

/-- `panSemBitVec64WordModel.byteAlign` is the exact HOL `byte_align` (clear the
    low `LOG2(width/8)` bits) at width 64. -/
theorem panSemBitVec64ByteAlign_eq_panByteAlignHOL (address : RiscV.Word 64) :
    panSemBitVec64WordModel.byteAlign (8 : RiscV.Word 64) address =
      panByteAlignHOL (width := 64) address := by
  have h8 : BitVec.toNat (8 : RiscV.Word 64) = 8 := by decide
  change RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address =
    panByteAlignHOL (width := 64) address
  simp only [RiscV.panRiscVByteAlign, panByteAlignHOL]
  rw [show Nat.log2 8 = 3 from rfl]
  apply BitVec.eq_of_toNat_eq
  have hlt : BitVec.toNat address / 8 * 8 < 2 ^ 64 := by
    have hle := Nat.div_mul_le_self (BitVec.toNat address) 8
    have his := BitVec.isLt address
    omega
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, h8]
  rw [if_neg (by decide : ¬ (8 = 0)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The model's `getByte` at width 64 equals the exact HOL `get_byte` codec
    `panRiscVGetByteEndian`, as a width-64 word. -/
theorem panSemBitVec64GetByte_eq_panRiscVGetByteEndian (address value : RiscV.Word 64)
    (bigEndian : Bool) :
    panSemBitVec64WordModel.getByte (8 : RiscV.Word 64) address value bigEndian =
      BitVec.ofNat 64
        (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value bigEndian).toNat := by
  have h8 : BitVec.toNat (8 : RiscV.Word 64) = 8 := by decide
  have hidx : 8 - BitVec.toNat address % 8 - 1 =
      8 - 1 - BitVec.toNat address % 8 := by
    have := Nat.mod_lt (BitVec.toNat address) (by decide : 0 < 8)
    omega
  cases bigEndian
  · simp only [panSemBitVec64WordModel, RiscV.panRiscVGetByteEndian,
      RiscV.panRiscVByteIndex, h8]
    simp only [if_neg (by decide : ¬ (8 = 0)), if_neg (by decide : ¬ (false = true))]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
  · simp only [panSemBitVec64WordModel, RiscV.panRiscVGetByteEndian,
      RiscV.panRiscVByteIndex, h8]
    simp only [if_neg (by decide : ¬ (8 = 0))]
    rw [hidx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- `panRiscVGetByteEndian` produces a byte (`< 256`). -/
theorem panRiscVGetByteEndian_toNat_lt_256 (address value : RiscV.Word 64)
    (bigEndian : Bool) :
    (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address value bigEndian).toNat < 256 := by
  simp only [RiscV.panRiscVGetByteEndian]
  rw [BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

/-- Executed `readByte` at BitVec 64 agrees with the tagged exact
    `panMemLoadByteHOL` (then widened with `BitVec.ofNat 64`). -/
theorem panSemBitVec64ReadByte_eq_panMemLoadByteHOL
    (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) (address : RiscV.Word 64) :
    (panSemBitVec64MemoryAccess state).readByte
        (panSemBitVec64MemoryAccess state).domain memory panSemBitVec64BytesInWord address =
      (panMemLoadByteHOL (width := 64) (panValueWordHOL memory)
          (fun a => state.memaddrs a && panValueWordDefined memory a = true) state.be
          address).map (fun byte => BitVec.ofNat 64 byte.toNat) := by
  simp only [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
    panSemBitVec64BytesInWord, panModelReadByte, panMemLoadByteHOL]
  rw [panSemBitVec64ByteAlign_eq_panByteAlignHOL address]
  simp only [panValueWordMemory]
  cases hcell : memory (panByteAlignHOL (width := 64) address) with
  | none => simp [panValueWordDefined, hcell]
  | some cell =>
      cases cell with
      | word w =>
          simp only [panValueWordHOL, panValueWordDefined, hcell,
            panSemBitVec64GetByte_eq_panRiscVGetByteEndian]
          cases hb : state.memaddrs (panByteAlignHOL (width := 64) address)
          · simp
          · simp only [(by decide : BitVec.ofNat 64 (64 / 8) = (8 : RiscV.Word 64))]
            simp
            change RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address w state.be =
              BitVec.ofNat 64 (BitVec.toNat
                (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address w state.be) % 256)
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (panRiscVGetByteEndian_toNat_lt_256 address w state.be)]
            exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
              (panRiscVGetByteEndian_toNat_lt_256 address w state.be)
              (by decide : 256 ≤ 2 ^ 64))).symm
      | rStruct fs => simp [panValueWordDefined, hcell]
      | nStruct nm fs => simp [panValueWordDefined, hcell]


/-! ## Executed-path read32 widening adapter (flapjack-pxn.18.3.6.9.2.1)

The executed BitVec-64 `read32` agrees with the tagged exact
`panMemLoad32HOL` (then widened with `BitVec.ofNat 64`).  These are untagged
production-side adapters. -/

theorem panSemBitVec64Aligned4_eq_decide (address : RiscV.Word 64) :
    panSemBitVec64WordModel.aligned 4 address =
      decide ((address >>> 2) <<< 2 = address) := by
  change RiscV.aligned address 4 = decide ((address >>> 2) <<< 2 = address)
  rw [RiscV.aligned]
  show (decide ((4 : Nat) ≠ 0) && decide (address.toNat % 4 = 0)) =
    decide ((address >>> 2) <<< 2 = address)
  rw [show decide ((4 : Nat) ≠ 0) = true from rfl, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h
    change BitVec.shiftLeft (BitVec.ushiftRight address 2) 2 = address
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft, BitVec.ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNatLT, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 2 = 4 from by decide]
    have hdvd : 4 ∣ BitVec.toNat address := Nat.dvd_of_mod_eq_zero h
    rw [Nat.mul_comm, Nat.mul_div_cancel' hdvd, Nat.mod_eq_of_lt (BitVec.isLt address)]
  · intro h
    have h2 : (BitVec.toNat address / 4 * 4) % 2 ^ 64 = BitVec.toNat address := by
      have hcong := congrArg BitVec.toNat h
      change BitVec.toNat (BitVec.shiftLeft (BitVec.ushiftRight address 2) 2) =
        BitVec.toNat address at hcong
      simp only [BitVec.shiftLeft, BitVec.ushiftRight, BitVec.toNat_ofNat,
        BitVec.toNat_ofNatLT, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
        show (2 : Nat) ^ 2 = 4 from by decide] at hcong
      exact hcong
    rw [← h2]
    rw [Nat.mod_mod_of_dvd _ (show 4 ∣ 2 ^ 64 from ⟨2 ^ 62, by decide⟩)]
    rw [Nat.mul_comm (BitVec.toNat address / 4) 4]
    exact Nat.mul_mod_right 4 _

theorem panRiscVWordOfBytes64_eq_widen (be : Bool) (b0 b1 b2 b3 : RiscV.Word 64)
    (h0 : b0.toNat < 256) (h1 : b1.toNat < 256)
    (h2 : b2.toNat < 256) (h3 : b3.toNat < 256) :
    RiscV.panRiscVWordOfBytes (width := 64) be [b0, b1, b2, b3] =
      BitVec.ofNat 64
        ((RiscV.panRiscVWordOfBytes (width := 32) be
          [BitVec.ofNat 32 b0.toNat, BitVec.ofNat 32 b1.toNat,
           BitVec.ofNat 32 b2.toNat, BitVec.ofNat 32 b3.toNat]).toNat) := by
  have hs : b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat < 2 ^ 32 := by
    omega
  have m0 : b0.toNat % 2 ^ 32 = b0.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h0 (by decide : 256 ≤ 2 ^ 32))
  have m1 : b1.toNat % 2 ^ 32 = b1.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (by decide : 256 ≤ 2 ^ 32))
  have m2 : b2.toNat % 2 ^ 32 = b2.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 (by decide : 256 ≤ 2 ^ 32))
  have m3 : b3.toNat % 2 ^ 32 = b3.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h3 (by decide : 256 ≤ 2 ^ 32))
  have hs' : b3.toNat + 256 * b2.toNat + 256 ^ 2 * b1.toNat + 256 ^ 3 * b0.toNat < 2 ^ 32 := by
    omega
  cases be
  · simp [RiscV.panRiscVWordOfBytes, Option.getD_some,
      m0, m1, m2, m3, Nat.mod_eq_of_lt hs]
  · simp [RiscV.panRiscVWordOfBytes, Option.getD_some,
      m0, m1, m2, m3, Nat.mod_eq_of_lt hs']


theorem panSemBitVec64WordOfBytes32_eq_widen (be : Bool) (x0 x1 x2 x3 : RiscV.Word 64)
    (h0 : x0.toNat < 256) (h1 : x1.toNat < 256)
    (h2 : x2.toNat < 256) (h3 : x3.toNat < 256) :
    panSemBitVec64WordModel.wordOfBytes32 be
        [BitVec.ofNat 64 x0.toNat, BitVec.ofNat 64 x1.toNat,
         BitVec.ofNat 64 x2.toNat, BitVec.ofNat 64 x3.toNat] =
      BitVec.ofNat 64
        ((RiscV.panRiscVWordOfBytes (width := 32) be
          [BitVec.ofNat 32 x0.toNat, BitVec.ofNat 32 x1.toNat,
           BitVec.ofNat 32 x2.toNat, BitVec.ofNat 32 x3.toNat]).toNat) := by
  change RiscV.panRiscVWordOfBytes (width := 64) be
      [BitVec.ofNat 64 x0.toNat, BitVec.ofNat 64 x1.toNat,
       BitVec.ofNat 64 x2.toNat, BitVec.ofNat 64 x3.toNat] = _
  rw [panRiscVWordOfBytes64_eq_widen be (BitVec.ofNat 64 x0.toNat) (BitVec.ofNat 64 x1.toNat)
        (BitVec.ofNat 64 x2.toNat) (BitVec.ofNat 64 x3.toNat)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt x0)]; exact h0)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt x1)]; exact h1)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt x2)]; exact h2)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt x3)]; exact h3)]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt x0),
    Nat.mod_eq_of_lt (BitVec.isLt x1), Nat.mod_eq_of_lt (BitVec.isLt x2),
    Nat.mod_eq_of_lt (BitVec.isLt x3)]

theorem panSemBitVec64Read32_eq_panMemLoad32HOL (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) (address : RiscV.Word 64) :
    (panSemBitVec64MemoryAccess state).read32
        (panSemBitVec64MemoryAccess state).domain memory panSemBitVec64BytesInWord address
      = (panMemLoad32HOL (width := 64) (panValueWordHOL memory)
          (fun a => state.memaddrs a && panValueWordDefined memory a = true) state.be
          address).map (fun word => BitVec.ofNat 64 word.toNat) := by
  simp only [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
    panSemBitVec64BytesInWord, panModelRead32, panMemLoad32HOL, panValueWordMemory]
  rw [panSemBitVec64ByteAlign_eq_panByteAlignHOL address, panSemBitVec64Aligned4_eq_decide address]
  cases hcell : memory (panByteAlignHOL (width := 64) address) with
  | none => simp [panValueWordDefined, hcell]
  | some cell =>
      cases cell with
      | word w =>
          simp only [panValueWordHOL, panValueWordDefined, hcell]
          simp
          simp only [show (8#64 : RiscV.Word 64) = (8 : RiscV.Word 64) from rfl,
            show (1#64 : RiscV.Word 64) = (1 : RiscV.Word 64) from rfl,
            show (2#64 : RiscV.Word 64) = (2 : RiscV.Word 64) from rfl,
            show (3#64 : RiscV.Word 64) = (3 : RiscV.Word 64) from rfl]
          simp only [panSemBitVec64GetByte_eq_panRiscVGetByteEndian]
          cases hb : state.memaddrs (panByteAlignHOL (width := 64) address)
          · simp
          · rw [panSemBitVec64WordOfBytes32_eq_widen state.be
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) address w state.be)
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 1) w state.be)
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 2) w state.be)
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64) (address + 3) w state.be)
              (panRiscVGetByteEndian_toNat_lt_256 address w state.be)
              (panRiscVGetByteEndian_toNat_lt_256 (address + 1) w state.be)
              (panRiscVGetByteEndian_toNat_lt_256 (address + 2) w state.be)
              (panRiscVGetByteEndian_toNat_lt_256 (address + 3) w state.be)]
            by_cases hg : address >>> 2 <<< 2 = address <;> simp
      | rStruct fs => simp [panValueWordDefined, hcell]
      | nStruct nm fs => simp [panValueWordDefined, hcell]

/-! ### Structured `.load` word-node bridge (flapjack-pxn.18.3.6.9.2.2)

The executed structured `.load` uses `panValueFlatLoad`; the tagged exact
`panMemLoadHOL` reads the same nodes.  The `One` clause is proved here; the
`Comb`/`Named` clauses require the fuel/context/offset machinery and are tracked
by the child bead `flapjack-pxn.18.3.6.9.2.2.1`. -/

theorem panValueFlatLoad_one_eq_panMemLoadHOL (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext) (address : RiscV.Word 64) :
    panValueFlatLoad structs memory panSemBitVec64BytesInWord address .one
        (some (panSemBitVec64MemoryAccess state)) =
      (panMemLoadHOL (width := 64) .one address
        (fun a => state.memaddrs a && panValueWordDefined memory a = true)
        (panValueWordHOL memory) structs.toHOL).map HolValue.toPanValue := by
  unfold panValueFlatLoad panMemLoadHOL
  simp only [isWfShape.eq_def, if_true]
  unfold panValueFlatLoadFuel panValueFlatReadWord
  unfold panSemBitVec64MemoryAccess panValueMemoryAccessOfModel
  simp only []
  cases hmem : memory address with
  | none => cases hd : state.memaddrs address <;> simp [hmem, panValueWordDefined]
  | some cell =>
      cases cell with
      | word w =>
          cases hd : state.memaddrs address <;>
            simp [hmem, panValueWordHOL, panValueWordDefined, HolValue.toPanValue]
      | rStruct fs =>
          cases hd : state.memaddrs address <;> simp [hmem, panValueWordDefined]
      | nStruct nm fs =>
          cases hd : state.memaddrs address <;> simp [hmem, panValueWordDefined]

/-! ### Structured `.load` fuel/offset helpers (flapjack-pxn.18.3.6.9.2.2/.2.2.1)

These untagged helpers connect the production fuel-indexed flattening load to the
tagged exact `panMemLoadHOL`: the production context-size agrees with the exact
`sizeOfShWithCtxt` over `StructContext.toHOL`, and the production offset
`panValueFlatOffset` agrees with the exact `address + bytes_in_word * n` step.
They are prerequisites for the remaining `Comb`/`Named` widening adapter
(`flapjack-pxn.18.3.6.9.2.2.1`). -/

theorem panValueFlatSizeFoldl_eq_sizeOfShWithCtxt (structs : StructContext) (shapes : List Shape)
    (acc : Nat)
    (h : ∀ shape ∈ shapes, shapeSizeWithContext structs shape = sizeOfShWithCtxt structs.toHOL shape) :
    shapes.foldl (fun total shape => total + shapeSizeWithContext structs shape) acc =
      shapes.foldl (fun total shape => total + sizeOfShWithCtxt structs.toHOL shape) acc := by
  induction shapes generalizing acc with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.foldl_cons]
      rw [h s List.mem_cons_self]
      exact ih (acc + sizeOfShWithCtxt structs.toHOL s) (fun x hx => h x (List.mem_cons_of_mem s hx))

theorem panValueFlatShapeSize_eq_sizeOfShWithCtxt (structs : StructContext) (shape : Shape) :
    shapeSizeWithContext structs shape = sizeOfShWithCtxt structs.toHOL shape := by
  induction shape using shapeSizeWithContext.induct with
  | case1 => simp only [shapeSizeWithContext, sizeOfShWithCtxt]
  | case2 shapes ih =>
      simp only [shapeSizeWithContext, sizeOfShWithCtxt]
      exact panValueFlatSizeFoldl_eq_sizeOfShWithCtxt structs shapes 0 ih
  | case3 name =>
      simp only [shapeSizeWithContext, sizeOfShWithCtxt]
      rw [lookupInfo_toHOL]
      cases lookupInfo name structs <;> rfl

theorem panValueFlatOffset_eq_widen (address : RiscV.Word 64) (n : Nat) :
    panValueFlatOffset (8 : RiscV.Word 64) address n =
      address + BitVec.ofNat 64 8 * BitVec.ofNat 64 n := by
  induction n generalizing address with
  | zero => simp [panValueFlatOffset]
  | succ n ih =>
      rw [panValueFlatOffset, ih]
      simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
      ac_rfl

/-! ### Fuel sufficiency for the structured `.load` adapter (flapjack-pxn.18.3.6.9.2.2.1)

The production flattening load passes the same fuel to each sub-shape; these
untagged Nat bounds show the freezer's initial fuel
`panValueFlatContextFuel structs + panValueFlatShapeFuel shape + 1` suffices for
every nested `Comb`/`Named` field. They are the remaining prerequisites for the
`Comb`/`Named` widening adapter to the tagged exact `panMemLoadHOL`. -/

theorem panValueFlatShapeFuel_le_listFuel {shape : Shape} {shapes : List Shape}
    (h : shape ∈ shapes) :
    panValueFlatShapeFuel shape ≤ panValueFlatShapeFuel.panValueFlatShapeListFuel shapes := by
  induction shapes with
  | nil => simp at h
  | cons head tail ih =>
      rcases List.mem_cons.mp h with hhead | htail
      · subst hhead
        simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel]
        omega
      · have hih := ih htail
        simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel]
        omega

theorem panValueFlatFieldsFuel_shapeFuel_le {field : FieldName × Shape}
    {fields : List (FieldName × Shape)} (h : field ∈ fields) :
    panValueFlatShapeFuel field.2 ≤ panValueFlatFieldsFuel fields := by
  induction fields with
  | nil => simp at h
  | cons head tail ih =>
      rcases List.mem_cons.mp h with hhead | htail
      · subst hhead
        simp only [panValueFlatFieldsFuel]
        omega
      · have hih := ih htail
        simp only [panValueFlatFieldsFuel]
        omega

theorem panValueFlatContextFuel_lookupInfoWithRest_le [BEq String] (name : String)
    (structs : StructContext) (info : StructInfo) (rest : StructContext)
    (h : lookupInfoWithRest name structs = some (info, rest)) :
    panValueFlatFieldsFuel info.fields + panValueFlatContextFuel rest ≤
      panValueFlatContextFuel structs := by
  induction structs with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry tail ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hc : candidate == name
      · simp [lookupInfoWithRest, hc] at h
        obtain ⟨hinfo, hrest⟩ := h
        subst hinfo; subst hrest
        simp [panValueFlatContextFuel]
      · simp only [lookupInfoWithRest, hc] at h
        have hih := ih h
        simp only [panValueFlatContextFuel]
        omega

/-! ### Per-node word read agreement (flapjack-pxn.18.3.6.9.2.2.1)

    The executed `PanSemBitVec64` memory access reads a word cell only when the
    address is in `state.memaddrs` and the cell holds a `.word`; the exact
    `panMemLoadHOL` reads the total `HolWordLab` view under the domain
    `state.memaddrs address && panValueWordDefined memory address = true`.  This
    lemma shows the production `panValueFlatReadWord` agrees with that exact
    domain/memory pair at every address. -/
theorem panValueFlatReadWord_eq_panValueWordHOL
    (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (address : RiscV.Word 64) :
    panValueFlatReadWord memory panSemBitVec64BytesInWord
        (some (panSemBitVec64MemoryAccess state)) address
      = (if state.memaddrs address && panValueWordDefined memory address = true
          then some (panValueWordHOL memory address) else none).map
          (fun lab => match lab with | .word value => value) := by
  unfold panValueFlatReadWord
  unfold panSemBitVec64MemoryAccess panValueMemoryAccessOfModel
  simp only []
  cases hmem : memory address with
  | none => cases hd : state.memaddrs address <;> simp [panValueWordDefined, hmem]
  | some cell =>
      cases cell with
      | word w =>
          cases hd : state.memaddrs address <;>
            simp [panValueWordHOL, panValueWordDefined, hmem]
      | rStruct fs =>
          cases hd : state.memaddrs address <;> simp [panValueWordDefined, hmem]
      | nStruct nm fs =>
          cases hd : state.memaddrs address <;> simp [panValueWordDefined, hmem]

/-! ### Structured `.load` Comb/Named induction prerequisites (flapjack-pxn.18.3.6.9.2.2.1)

Fuel positivity facts for the production flattening load and the not-found named-scan
agreement between `lookupInfoWithRest` and the tagged exact `panMemLoadHOL`. -/

/-- Fuel positivity: the shape fuel is always at least one. -/
theorem panValueFlatShapeFuel_pos (shape : Shape) : 1 ≤ panValueFlatShapeFuel shape := by
  cases shape <;> simp only [panValueFlatShapeFuel] <;> omega

/-- Fuel positivity: a nonempty shape list has list fuel at least one. -/
theorem panValueFlatShapeListFuel_pos (shape : Shape) (shapes : List Shape) :
    1 ≤ panValueFlatShapeFuel.panValueFlatShapeListFuel (shape :: shapes) := by
  simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel]
  omega

/-- Fuel positivity: a nonempty field list has field fuel at least one. -/
theorem panValueFlatFieldsFuel_pos (field : FieldName × Shape)
    (fields : List (FieldName × Shape)) :
    1 ≤ panValueFlatFieldsFuel (field :: fields) := by
  obtain ⟨name, shape⟩ := field
  simp only [panValueFlatFieldsFuel]
  omega

/-- Named-scan agreement: when `lookupInfoWithRest` fails to find the name, the tagged exact
structured load of `.named name` over the HOL-shaped context is `none` as well. -/
theorem panMemLoadHOL_named_none (name : StructName) (structs : StructContext)
    (address : RiscV.Word 64) (domain : RiscV.Word 64 → Prop) [DecidablePred domain]
    (memory : RiscV.Word 64 → HolWordLab 64)
    (h : lookupInfoWithRest name structs = none) :
    panMemLoadHOL (width := 64) (.named name) address domain memory structs.toHOL = none := by
  induction structs with
  | nil => simp [StructContext.toHOL, panMemLoadHOL]
  | cons entry rest ih =>
      obtain ⟨candidate, info⟩ := entry
      simp only [StructContext.toHOL, List.map_cons, lookupInfoWithRest] at h ⊢
      by_cases hc : candidate == name
      · simp [hc] at h
      · have hrest : lookupInfoWithRest name rest = none := by simpa [hc] using h
        rw [panMemLoadHOL.eq_def]
        simp only [hc, Bool.false_eq_true, if_false]
        exact ih hrest

end Flapjack
