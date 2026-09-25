import Flapjack.Compiler.Encoders.Asm
import Flapjack.PanBst
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
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
  let alignment := 2 ^ Nat.log2 (width / 8)
  BitVec.ofNat width ((address.toNat / alignment) * alignment)

/-- Flapjack-specific BitVec rendering of HOL4 standard-library
`byte$get_byte_def` and `byte_index_def` from
`HOL/src/n-bit/byteScript.sml:15-23`. This dependency is outside the CakeML
repository, so this helper intentionally has no repository `@[hol]` tag. The
formula preserves HOL natural `MOD 0` and subtraction behavior for sub-byte
dimensions. -/
def panGetByteHOL {width : Nat} (address value : RiscV.Word width)
    (bigEndian : Bool) : UInt8 :=
  let bytesPerWord := width / 8
  let byteIndex := if bigEndian then
      bytesPerWord - 1 - (address.toNat % bytesPerWord)
    else address.toNat % bytesPerWord
  UInt8.ofNat ((value.toNat / 256 ^ byteIndex) % 256)

/-- HOL `byte$get_byte_def`/`byte_index_def` specialized to the source word
    width. In particular, little endian `w2n address MOD 0` keeps the address
    as the shift index below one byte. The RISC-V memory helper returns index
    zero when `bytesInWord = 0`, which differs. The executed
    `PanValueMemoryAccess.readByte` widening adapter remains tracked by
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
        some (panGetByteHOL address value bigEndian)
      else none

/-- Exact port of HOL `mem_load_32_def`
    (`cakeml/pancake/semantics/panSemScript.sml:94-104`).  When `aligned 2` holds
    at the address, the four consecutive bytes `w`, `w+1`, `w+2`, `w+3` of the
    stored word are reassembled (in the requested byte order) into a `word32`;
    out-of-domain or unaligned addresses yield `NONE`.  As in
    `panMemLoadByteHOL`, HOL's total `word_lab` memory is rendered as a total
    map into `HolWordLab` and the `word set` domain as a `Prop` predicate.
    `aligned 2` is `w2n address MOD 4 = 0`; writing this directly avoids
    BitVec's overloaded shift notation choosing a word-sized shift amount,
    which truncates literal 2 to zero for one-bit words. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_32_def"]
def panMemLoad32HOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option (RiscV.Word 32) :=
  if address.toNat % 4 = 0 then
    let aligned := panByteAlignHOL (width := width) address
    match memory aligned with
    | .word value =>
        if domain aligned then
          let getByte := fun currentAddress =>
            BitVec.ofNat width (panGetByteHOL currentAddress value bigEndian).toNat
          let bytes :=
            [ getByte address,
              getByte (address + 1),
              getByte (address + 2),
              getByte (address + 3) ]
          some (RiscV.panRiscVWordOfBytes (width := 32) bigEndian
            (bytes.map (fun byte => BitVec.ofNat 32 byte.toNat)))
        else none
  else none


/-- Flapjack-specific BitVec rendering of HOL4 standard-library
`byte$set_byte_def` (`HOL/src/n-bit/byteScript.sml`), the inverse of
`panGetByteHOL`: replace the byte at the endian-adjusted byte index by
`byteValue`.  As with `panGetByteHOL` this dependency is outside the CakeML
repository, so the helper intentionally has no repository `@[hol]` tag. -/
def panSetByteHOL {width : Nat} (address byteValue cell : RiscV.Word width)
    (bigEndian : Bool) : RiscV.Word width :=
  let bytesPerWord := width / 8
  let byteIndex := address.toNat % bytesPerWord
  let byteIndex := if bigEndian then bytesPerWord - byteIndex - 1 else byteIndex
  let offset := 256 ^ byteIndex
  let block := offset * 256
  let low := cell.toNat % offset
  let high := cell.toNat / block
  BitVec.ofNat width (low + (byteValue.toNat % 256) * offset + high * block)

/-- Exact port of HOL `panSem$mem_store_byte`
    (`cakeml/pancake/semantics/panSemScript.sml:300-307`):
    `mem_store_byte m dm be w b = case m (byte_align w) of Word v =>
    if byte_align w IN dm then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
    else NONE`.  As in `panMemLoadByteHOL`, HOL's total `word_lab` memory is a
    total map into `HolWordLab` and the `word set` domain a `Prop` predicate. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_store_byte_def"]
def panMemStoreByteHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (byte : UInt8) :
    Option (RiscV.Word width → HolWordLab width) :=
  let aligned := panByteAlignHOL (width := width) address
  match memory aligned with
  | .word cell =>
      if domain aligned then
        some (fun current =>
          if current = aligned then
            .word (panSetByteHOL address (BitVec.ofNat width byte.toNat) cell
              bigEndian)
          else memory current)
      else none

/-- Exact port of HOL `panSem$write_bytearray`
    (`cakeml/pancake/semantics/panSemScript.sml:309-316`):
    `write_bytearray a [] m dm be = m` and
    `write_bytearray a (b::bs) m dm be = case mem_store_byte
    (write_bytearray (a+1) bs m dm be) dm be a b of SOME m => m | NONE => m`
    (a failed store keeps the original outer memory). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "write_bytearray_def" 309]
def panWriteBytearrayHOL {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) : RiscV.Word width → HolWordLab width :=
  match bytes with
  | [] => memory
  | byte :: rest =>
      match panMemStoreByteHOL
          (panWriteBytearrayHOL (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | some updated => updated
      | none => memory


/-- Exact port of HOL `panSem$mem_store_32`
    (`cakeml/pancake/semantics/panSemScript.sml:327-346`).  When `aligned 2`
    holds, the four bytes of the `word32` argument are written at `w`, `w+1`,
    `w+2`, `w+3` in the requested byte order (each via `set_byte`) and the
    aligned cell is replaced; unaligned or out-of-domain addresses yield `NONE`.
    As in the other memory ports, HOL's total `word_lab` memory is a total map
    into `HolWordLab` and the `word set` domain a `Prop` predicate.  `aligned 2`
    is written as `w2n w MOD 4 = 0` to avoid BitVec's overloaded shift notation
    truncating literal `2` for one-bit words. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_store_32_def"]
def panMemStore32HOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (value : RiscV.Word 32) :
    Option (RiscV.Word width → HolWordLab width) :=
  if address.toNat % 4 = 0 then
    let aligned := panByteAlignHOL (width := width) address
    match memory aligned with
    | .word cell =>
        if domain aligned then
          let getByte := fun (index : Nat) =>
            panGetByteHOL (width := 32) (BitVec.ofNat 32 index) value bigEndian
          let setByte := fun (index : Nat) (byte : UInt8)
              (current : RiscV.Word width) =>
            panSetByteHOL (address + BitVec.ofNat width index)
              (BitVec.ofNat width byte.toNat) current bigEndian
          let cell0 := setByte 0 (getByte 0) cell
          let cell1 := setByte 1 (getByte 1) cell0
          let cell2 := setByte 2 (getByte 2) cell1
          let cell3 := setByte 3 (getByte 3) cell2
          some (fun current => if current = aligned then .word cell3 else memory current)
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

/-! Statement-exact port of HOL `panSem$mem_store` and `mem_stores`
    (`cakeml/pancake/semantics/panSemScript.sml:373-386`).  Both operate on the
    total `HolWordLab` memory with a `Prop` domain (HOL `'a word set`); HOL's
    `addr =+ w` update is the pointwise function update below, and the address
    stride is the canonical `panBytesInWord width` (HOL's global
    `bytes_in_word = n2w (dimindex(:'a) DIV 8)`, no free parameter). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_store_def"]
def panMemStoreHOL {width : Nat} [NeZero width] (address : RiscV.Word width) (value : HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) :
    Option (RiscV.Word width → HolWordLab width) :=
  if domain address then
    some (fun current => if current = address then value else memory current)
  else none

@[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_stores_def"]
def panMemStoresHOL {width : Nat} [NeZero width] (address : RiscV.Word width)
    (values : List (HolWordLab width)) (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) :
    Option (RiscV.Word width → HolWordLab width) :=
  match values with
  | [] => some memory
  | value :: rest =>
      match panMemStoreHOL address value domain memory with
      | some updated => panMemStoresHOL (address + panBytesInWord width) rest domain updated
      | none => none

@[simp] theorem panMemStoreHOL_hit {width : Nat} [NeZero width] (address : RiscV.Word width)
    (value : HolWordLab width) (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) (h : domain address) :
    panMemStoreHOL address value domain memory
      = some (fun current => if current = address then value else memory current) := by
  simp only [panMemStoreHOL, if_pos h]

theorem panMemStoreHOL_miss {width : Nat} [NeZero width] (address : RiscV.Word width)
    (value : HolWordLab width) (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) (h : ¬ domain address) :
    panMemStoreHOL address value domain memory = none := by
  simp only [panMemStoreHOL, if_neg h]

@[simp] theorem panMemStoresHOL_nil {width : Nat} [NeZero width] (address : RiscV.Word width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width) :
    panMemStoresHOL address [] domain memory = some memory := rfl

theorem panMemStoresHOL_cons_some {width : Nat} [NeZero width] (address : RiscV.Word width)
    (value : HolWordLab width) (rest : List (HolWordLab width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory updated : RiscV.Word width → HolWordLab width)
    (h : panMemStoreHOL address value domain memory = some updated) :
    panMemStoresHOL address (value :: rest) domain memory
      = panMemStoresHOL (address + panBytesInWord width) rest domain updated := by
  simp only [panMemStoresHOL, h]

theorem panMemStoresHOL_cons_none {width : Nat} [NeZero width] (address : RiscV.Word width)
    (value : HolWordLab width) (rest : List (HolWordLab width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (memory : RiscV.Word width → HolWordLab width)
    (h : panMemStoreHOL address value domain memory = none) :
    panMemStoresHOL address (value :: rest) domain memory = none := by
  simp only [panMemStoresHOL, h]

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
    with the remaining context, exactly the `(nm,info)::stcs'` HOL destructures.

    Two Lean-only binders are worth spelling out.  Each function carries
    `[NeZero width]`: HOL words always have a positive dimension
    (`dimindex (:'a) > 0`), so `width = 0` is not a HOL instance and the tagged
    statements must not admit it.  The `[DecidablePred domain]` binder is
    likewise only Lean decidability evidence, needed so that the `if domain
    address` branch elaborates; it is not a HOL side condition (HOL `domain` is
    a `'a word set` and membership is a `bool`-valued test there).

    DELIBERATELY UNTAGGED: HOL `panLang$shape` and the structure/field names in
    the context are `mlstring`, while the Lean carriers used here (`Shape`
    names, `StructContextHOL`, `FieldName`) are `String` (`Flapjack/Pancake/PanLang.lean:15,28,67`).
    Retagging requires an exact `MlString`-keyed `ShapeHOL`/context carrier; that
    substitution is tracked by bead `flapjack-pxn.18.5.17.1.2.1`.  The `[NeZero
    width]` improvement and the untagged implementation remain valid. -/
mutual
  def panMemLoadHOL {width : Nat} [NeZero width] (shape : Shape) (address : RiscV.Word width)
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

  def panMemLoadsHOL {width : Nat} [NeZero width] (shapes : List Shape) (address : RiscV.Word width)
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

  def panMemLoadFldsHOL {width : Nat} [NeZero width] (fields : List (FieldName × Shape)) (address : RiscV.Word width)
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
  rfl

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

/-- The Flapjack-specific HOL byte codec agrees with the RISC-V endian byte
    helper at the production width 64. -/
theorem panGetByteHOL_eq_panRiscVGetByteEndian (address value : RiscV.Word 64)
    (bigEndian : Bool) :
    panGetByteHOL address value bigEndian =
      UInt8.ofNat (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
        address value bigEndian).toNat := by
  unfold panGetByteHOL
  apply congrArg UInt8.ofNat
  simp [RiscV.panRiscVGetByteEndian, RiscV.panRiscVByteIndex]
  have hsmall :
      (value.toNat / 256 ^
        (if bigEndian = true then 7 - address.toNat % 8
         else address.toNat % 8)) % 256 < 2 ^ 64 := by
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hsmall]

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
          · simp
            have hbyte : panGetByteHOL address w state.be =
                UInt8.ofNat
                  (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
                    address w state.be).toNat := by
              unfold panGetByteHOL
              apply congrArg UInt8.ofNat
              simp [RiscV.panRiscVGetByteEndian, RiscV.panRiscVByteIndex]
              have hsmall :
                  (w.toNat / 256 ^
                    (if state.be = true then 7 - address.toNat % 8
                     else address.toNat % 8)) % 256 < 2 ^ 64 := by
                exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
              rw [Nat.mod_eq_of_lt hsmall]
            rw [hbyte]
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
      decide (address.toNat % 4 = 0) := by
  change RiscV.aligned address 4 = decide (address.toNat % 4 = 0)
  simp [RiscV.aligned]

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
          simp only [panSemBitVec64GetByte_eq_panRiscVGetByteEndian,
            panGetByteHOL_eq_panRiscVGetByteEndian]
          have hbyte0 := panRiscVGetByteEndian_toNat_lt_256 address w state.be
          have hbyte1 := panRiscVGetByteEndian_toNat_lt_256 (address + 1) w state.be
          have hbyte2 := panRiscVGetByteEndian_toNat_lt_256 (address + 2) w state.be
          have hbyte3 := panRiscVGetByteEndian_toNat_lt_256 (address + 3) w state.be
          have hu0 : (UInt8.ofNat (RiscV.panRiscVGetByteEndian
              (8 : RiscV.Word 64) address w state.be).toNat).toNat =
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
                address w state.be).toNat := by
            exact UInt8.toNat_ofNat_of_lt hbyte0
          have hu1 : (UInt8.ofNat (RiscV.panRiscVGetByteEndian
              (8 : RiscV.Word 64) (address + 1) w state.be).toNat).toNat =
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
                (address + 1) w state.be).toNat := by
            exact UInt8.toNat_ofNat_of_lt hbyte1
          have hu2 : (UInt8.ofNat (RiscV.panRiscVGetByteEndian
              (8 : RiscV.Word 64) (address + 2) w state.be).toNat).toNat =
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
                (address + 2) w state.be).toNat := by
            exact UInt8.toNat_ofNat_of_lt hbyte2
          have hu3 : (UInt8.ofNat (RiscV.panRiscVGetByteEndian
              (8 : RiscV.Word 64) (address + 3) w state.be).toNat).toNat =
              (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
                (address + 3) w state.be).toNat := by
            exact UInt8.toNat_ofNat_of_lt hbyte3
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
            rw [hu0, hu1, hu2, hu3]
            by_cases hg : address.toNat % 4 = 0 <;> simp [hg]
      | rStruct fs => simp [panValueWordDefined, hcell]
      | nStruct nm fs => simp [panValueWordDefined, hcell]

/-! ### Structured `.load` word-node bridge (flapjack-pxn.18.3.6.9.2.2)

The executed structured `.load` uses `panValueFlatLoad`; the HOL-shaped
(core currently untagged) `panMemLoadHOL` reads the same nodes.  The `One` clause is proved here; the
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
  simp only [isWfShape.eq_def, isWfShapeHOL_one, if_true]
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
HOL-shaped (core currently untagged) `panMemLoadHOL`: the production context-size agrees with the exact
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
`Comb`/`Named` widening adapter to the HOL-shaped (core currently
untagged) `panMemLoadHOL`. -/

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
agreement between `lookupInfoWithRest` and the HOL-shaped (core currently
untagged) `panMemLoadHOL`. -/

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

/-- Named-scan agreement: when `lookupInfoWithRest` fails to find the name, the HOL-shaped
(core currently untagged) structured load of `.named name` over the HOL-shaped context is `none`
as well. -/
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

/-- Named-scan agreement, found case: when `lookupInfoWithRest` finds the name with tail `rest`,
the HOL-shaped (core currently untagged) structured load of `.named name` over the HOL-shaped context loads the fields of
the found `info` under the tail context `rest`.  The result is stated through `Option.map` (rather
than a `match`) so that the equality is well-defined for `rfl`/`simp` comparisons. -/
theorem panMemLoadHOL_named_some (name : StructName) (structs : StructContext)
    (address : RiscV.Word 64) (domain : RiscV.Word 64 → Prop) [DecidablePred domain]
    (memory : RiscV.Word 64 → HolWordLab 64) (info : StructInfo) (rest : StructContext)
    (h : lookupInfoWithRest name structs = some (info, rest)) :
    panMemLoadHOL (width := 64) (.named name) address domain memory structs.toHOL =
      (panMemLoadFldsHOL info.fields address domain memory rest.toHOL).map
        (fun fields => HolValue.nStruct name fields) := by
  induction structs with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry rest' ih =>
      obtain ⟨candidate, info'⟩ := entry
      simp only [StructContext.toHOL, List.map_cons] at h ⊢
      cases hb : candidate == name
      · simp only [lookupInfoWithRest, hb] at h
        rw [panMemLoadHOL.eq_def]
        simp only [hb, Bool.false_eq_true, if_false]
        exact ih h
      · simp only [lookupInfoWithRest, hb, if_true] at h
        obtain ⟨rfl, rfl⟩ := Option.some.inj h
        have hc : candidate = name := beq_iff_eq.mp hb
        subst hc
        rw [panMemLoadHOL.eq_def]
        simp only [hb, if_true]
        split <;> simp_all [Option.map]

/-! The equation lemmas of the exact-HOL value isomorphism `HolValue.toPanValue`
    (`cakeml/pancake/semantics/panSemScript.sml:22`), needed to push `Option.map
    HolValue.toPanValue` through the structured `mem_load` cases of the executed
    `.load` widening adapter (flapjack-pxn.18.3.6.9.2.2.1).  Untagged
    production-side helpers. -/

theorem HolValue.toPanValue_val {width : Nat} (bits : RiscV.Word width) :
    HolValue.toPanValue (width := width) (HolValue.val (HolWordLab.word bits)) =
      PanValue.word bits := by
  rw [HolValue.toPanValue]

theorem HolValue.toPanValue_rStruct {width : Nat} (fields : List (HolValue width)) :
    HolValue.toPanValue (width := width) (HolValue.rStruct fields) =
      PanValue.rStruct (fields.map HolValue.toPanValue) := by
  rw [HolValue.toPanValue]

theorem HolValue.toPanValue_nStruct {width : Nat} (name : StructName)
    (fields : List (FieldName × HolValue width)) :
    HolValue.toPanValue (width := width) (HolValue.nStruct name fields) =
      PanValue.nStruct name (fields.map (fun p => (p.1, HolValue.toPanValue p.2))) := by
  rw [HolValue.toPanValue]

/-! ## Structured `.load` fuel-indexed equivalence (flapjack-pxn.18.3.6.9.2.2.1.1.2/.3)

Kernel-checked equivalence between the production fuel-indexed flattening loader and
the `mem_load_def`-shaped port for arbitrary Comb/List/Fields/Named shapes, under the
executed RV64 memory-access state.  The port is currently UNTAGGED pending an exact
`MlString`-keyed `ShapeHOL`/context carrier (bead flapjack-pxn.18.5.17.1.2.1); this is
an untagged production-side adapter. -/

abbrev panValueFlatMachineReadWord (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) : RiscV.Word 64 → Option (RiscV.Word 64) :=
  panValueFlatReadWord memory panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state))

abbrev panValueFlatMachineDomain (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) : RiscV.Word 64 → Prop :=
  fun a => state.memaddrs a && panValueWordDefined memory a = true

theorem panValueFlatLoadFuel_eq_panMemLoadHOL (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64))) :
    ∀ (fuel : Nat),
      (∀ (structs : StructContext) (shape : Shape) (address : RiscV.Word 64),
        panValueFlatContextFuel structs + panValueFlatShapeFuel shape ≤ fuel →
        panValueFlatLoadFuel structs (panValueFlatMachineReadWord state memory) panSemBitVec64BytesInWord fuel shape address
          = (panMemLoadHOL (width := 64) shape address (panValueFlatMachineDomain state memory)
              (panValueWordHOL memory) structs.toHOL).map HolValue.toPanValue)
      ∧ (∀ (structs : StructContext) (shapes : List Shape) (address : RiscV.Word 64),
        panValueFlatContextFuel structs + panValueFlatShapeFuel.panValueFlatShapeListFuel shapes ≤ fuel →
        panValueFlatLoadListFuel structs (panValueFlatMachineReadWord state memory) panSemBitVec64BytesInWord fuel shapes address
          = (panMemLoadsHOL shapes address (panValueFlatMachineDomain state memory)
              (panValueWordHOL memory) structs.toHOL).map (List.map HolValue.toPanValue))
      ∧ (∀ (structs : StructContext) (fields : List (FieldName × Shape)) (address : RiscV.Word 64),
        panValueFlatContextFuel structs + panValueFlatFieldsFuel fields ≤ fuel →
        panValueFlatLoadFieldsFuel structs (panValueFlatMachineReadWord state memory) panSemBitVec64BytesInWord fuel fields address
          = (panMemLoadFldsHOL fields address (panValueFlatMachineDomain state memory)
              (panValueWordHOL memory) structs.toHOL).map
              (List.map (fun p => (p.1, HolValue.toPanValue p.2)))) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro structs shape address h
        have := panValueFlatShapeFuel_pos shape
        omega
      · intro structs shapes address h
        cases shapes with
        | nil => simp [panValueFlatLoadListFuel, panMemLoadsHOL]
        | cons shape shapes =>
            simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel] at h
            have := panValueFlatShapeFuel_pos shape
            omega
      · intro structs fields address h
        cases fields with
        | nil => simp [panValueFlatLoadFieldsFuel, panMemLoadFldsHOL]
        | cons field fields =>
            obtain ⟨_, shape⟩ := field
            simp only [panValueFlatFieldsFuel] at h
            have := panValueFlatShapeFuel_pos shape
            omega
  | succ fuel ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro structs shape address h
        cases shape with
        | one =>
            simp only [panValueFlatLoadFuel]
            simp only [panValueFlatMachineReadWord]
            rw [panMemLoadHOL.eq_def]
            simp only []
            rw [panValueFlatReadWord_eq_panValueWordHOL]
            cases hmem : memory address with
            | none => simp [panValueFlatMachineDomain, panValueWordDefined, hmem]
            | some cell =>
                cases cell with
                | word w =>
                    simp [panValueFlatMachineDomain, panValueWordDefined, hmem, panValueWordHOL,
                      HolValue.toPanValue_val]
                | rStruct fs => simp [panValueFlatMachineDomain, panValueWordDefined, hmem]
                | nStruct nm fs => simp [panValueFlatMachineDomain, panValueWordDefined, hmem]
        | comb shapes =>
            simp only [panValueFlatLoadFuel]
            rw [panMemLoadHOL.eq_def]
            simp only []
            have hb : panValueFlatContextFuel structs
                + panValueFlatShapeFuel.panValueFlatShapeListFuel shapes ≤ fuel := by
              simp only [panValueFlatShapeFuel] at h
              omega
            rw [ih.2.1 structs shapes address hb]
            cases panMemLoadsHOL shapes address (panValueFlatMachineDomain state memory)
                (panValueWordHOL memory) structs.toHOL <;>
              simp [HolValue.toPanValue_rStruct]
        | named name =>
            simp only [panValueFlatLoadFuel]
            cases hlook : lookupInfoWithRest name structs with
            | none =>
                rw [panMemLoadHOL_named_none name structs address (panValueFlatMachineDomain state memory)
                  (panValueWordHOL memory) hlook]
                simp
            | some pair =>
                obtain ⟨info, rest⟩ := pair
                have hb : panValueFlatContextFuel rest + panValueFlatFieldsFuel info.fields ≤ fuel := by
                  have hle := panValueFlatContextFuel_lookupInfoWithRest_le name structs info rest hlook
                  simp only [panValueFlatShapeFuel] at h
                  omega
                rw [panMemLoadHOL_named_some name structs address (panValueFlatMachineDomain state memory)
                  (panValueWordHOL memory) info rest hlook]
                simp
                rw [ih.2.2 rest info.fields address hb]
                cases panMemLoadFldsHOL info.fields address (panValueFlatMachineDomain state memory)
                    (panValueWordHOL memory) rest.toHOL <;>
                  simp [HolValue.toPanValue_nStruct]
      · intro structs shapes address h
        cases shapes with
        | nil => simp [panValueFlatLoadListFuel, panMemLoadsHOL]
        | cons shape shapes =>
            simp only [panValueFlatLoadListFuel]
            rw [panMemLoadsHOL.eq_def]
            simp only []
            have hshape : panValueFlatContextFuel structs + panValueFlatShapeFuel shape ≤ fuel := by
              simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel] at h
              omega
            have htail : panValueFlatContextFuel structs
                + panValueFlatShapeFuel.panValueFlatShapeListFuel shapes ≤ fuel := by
              simp only [panValueFlatShapeFuel.panValueFlatShapeListFuel] at h
              omega
            have haddr : panValueFlatOffset panSemBitVec64BytesInWord address
                    (shapeSizeWithContext structs shape)
                = address + panBytesInWord 64
                    * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape) := by
              rw [show panSemBitVec64BytesInWord = (8 : RiscV.Word 64) from rfl,
                panValueFlatOffset_eq_widen]
              simp only [panValueFlatShapeSize_eq_sizeOfShWithCtxt, panBytesInWord]
            rw [haddr]
            rw [ih.1 structs shape address hshape]
            rw [ih.2.1 structs shapes
              (address + panBytesInWord 64 * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape)) htail]
            cases panMemLoadHOL shape address (panValueFlatMachineDomain state memory)
                (panValueWordHOL memory) structs.toHOL <;>
              cases panMemLoadsHOL shapes
                (address + panBytesInWord 64 * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape))
                (panValueFlatMachineDomain state memory) (panValueWordHOL memory) structs.toHOL <;>
              simp
      · intro structs fields address h
        cases fields with
        | nil => simp [panValueFlatLoadFieldsFuel, panMemLoadFldsHOL]
        | cons field fields =>
            obtain ⟨fieldName, shape⟩ := field
            simp only [panValueFlatLoadFieldsFuel]
            rw [panMemLoadFldsHOL.eq_def]
            simp only []
            have hshape : panValueFlatContextFuel structs + panValueFlatShapeFuel shape ≤ fuel := by
              simp only [panValueFlatFieldsFuel] at h
              omega
            have htail : panValueFlatContextFuel structs + panValueFlatFieldsFuel fields ≤ fuel := by
              simp only [panValueFlatFieldsFuel] at h
              omega
            have haddr : panValueFlatOffset panSemBitVec64BytesInWord address
                    (shapeSizeWithContext structs shape)
                = address + panBytesInWord 64
                    * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape) := by
              rw [show panSemBitVec64BytesInWord = (8 : RiscV.Word 64) from rfl,
                panValueFlatOffset_eq_widen]
              simp only [panValueFlatShapeSize_eq_sizeOfShWithCtxt, panBytesInWord]
            rw [haddr]
            rw [ih.1 structs shape address hshape]
            rw [ih.2.2 structs fields
              (address + panBytesInWord 64 * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape)) htail]
            cases panMemLoadHOL shape address (panValueFlatMachineDomain state memory)
                (panValueWordHOL memory) structs.toHOL <;>
              cases panMemLoadFldsHOL fields
                (address + panBytesInWord 64 * BitVec.ofNat 64 (sizeOfShWithCtxt structs.toHOL shape))
                (panValueFlatMachineDomain state memory) (panValueWordHOL memory) structs.toHOL <;>
              simp

/-! ## Structured `.load` capstone (flapjack-pxn.18.3.6.9.2.2)

The production `panValueFlatLoad` guards on `isWfShape` and starts the fuel at
`panValueFlatContextFuel + panValueFlatShapeFuel + 1`.  Combining that with the
fuel-indexed equivalence above and the initial-fuel bound yields the executed
`.load` result as the HOL `mem_load_def`-shaped port (currently untagged pending an
exact `MlString`-keyed carrier; bead flapjack-pxn.18.5.17.1.2.1).  Untagged
production-side adapter. -/

theorem panValueFlatLoad_eq_panMemLoadHOL (state : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext) (shape : Shape) (address : RiscV.Word 64)
    (hwf : isWfShape structs shape = true) :
    panValueFlatLoad structs memory panSemBitVec64BytesInWord address shape
        (some (panSemBitVec64MemoryAccess state))
      = (panMemLoadHOL (width := 64) shape address (panValueFlatMachineDomain state memory)
          (panValueWordHOL memory) structs.toHOL).map HolValue.toPanValue := by
  simp only [panValueFlatLoad, hwf, if_true]
  exact (panValueFlatLoadFuel_eq_panMemLoadHOL state memory
      (panValueFlatContextFuel structs + panValueFlatShapeFuel shape + 1)).1
    structs shape address (by omega)

/-! ## HOL-shaped `panSem$eval_def` expression adapter (flapjack-pxn.18.3.6.9.3)

The clauses below follow Cake's `eval_def`
(`cakeml/pancake/semantics/panSemScript.sml:209-283`), but the adapter is not
an exact HOL port and is untagged: its `HolValue` and struct context still use
Lean `String` where HOL uses `mlstring`. In particular, lawful `String`
equality proves only the adapter's own field-name comparisons, not the
corresponding HOL statement. The exact value carrier is being introduced in
`PanSem/ValueHOL.lean`; an exact source-state/evaluator route remains tracked
by `flapjack-0lj` and `flapjack-pxn.18.3.5.8`.

The structured-load helper `panMemLoadHOL` is likewise untagged pending the
exact MlString-keyed shape/context carrier (`flapjack-pxn.18.5.17.1.3`).
`bytes_in_word` is modeled by `n2w (dimindex(:'a) DIV 8)`, and the domain
predicate's `[DecidablePred]` supplies Lean decision evidence for HOL set
membership; neither removes the identifier-carrier gap. -/

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): clause-for-clause the
    same as HOL `shape_of` (`cakeml/pancake/semantics/panSemScript.sml:80`), but
    it recurses over the String-bearing `HolValue` carrier whose `nStruct` name
    is `StructName = String` and returns `Shape.named (StructName)`, whereas HOL
    `v`'s `stcname`/`fldname` and `shape`'s `Named` argument are `mlstring`.
    The `@[hol]` tag is therefore withheld (bead `flapjack-0lj`); the exact
    MlString-keyed carrier port is tracked by `flapjack-pxn.18.3.5.8`.  Kept for
    the untagged `evalHOL` adapter.  Carries `[NeZero width]` because HOL word
    types have positive `dimindex`. -/
def holShapeOf {width : Nat} [NeZero width] : HolValue width → Shape
  | .val _ => .one
  | .rStruct values => .comb (values.map holShapeOf)
  | .nStruct name _ => .named name
termination_by value => sizeOf value

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): same clauses as HOL
    `isValWord` (`cakeml/pancake/semantics/panSemScript.sml:35`), but over the
    String-bearing `HolValue` carrier (HOL `v` uses `stcname`/`fldname` =
    `mlstring`).  The `@[hol]` tag is therefore withheld (bead `flapjack-0lj`);
    the exact carrier counterpart is `isValWordHOL` in
    `PanSem/ValueHOL.lean`.  The word-only port `isWordHOL` over `HolWordLab`
    below also stays exact.  Carries `[NeZero width]` because HOL word types
    have positive `dimindex`. -/
def holValueIsWord {width : Nat} [NeZero width] : HolValue width → Bool
  | .val (.word _) => true
  | _ => false

/-- Exact port of HOL `isWord` (`cakeml/pancake/semantics/panSemScript.sml:28`)
    over the width-indexed one-constructor `word_lab` carrier `HolWordLab`.
    Carries `[NeZero width]` because HOL word types have positive `dimindex`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "isWord_def"]
def isWordHOL {width : Nat} [NeZero width] : HolWordLab width → Bool
  | .word _ => true

/-- Exact port of HOL `theWord` (`cakeml/pancake/semantics/panSemScript.sml:33`)
    over the width-indexed one-constructor `word_lab` carrier `HolWordLab`.
    HOL's `theWord_def` only patterns `Word w`, which is total for the
    one-constructor datatype, so this is a complete exact port.  Carries
    `[NeZero width]` because HOL word types have positive `dimindex`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "theWord_def"]
def theWordHOL {width : Nat} [NeZero width] : HolWordLab width → BitVec width
  | .word value => value

@[simp] theorem isWordHOL_word {width : Nat} [NeZero width] (value : BitVec width) :
    isWordHOL (HolWordLab.word value) = true := rfl

@[simp] theorem theWordHOL_word {width : Nat} [NeZero width] (value : BitVec width) :
    theWordHOL (HolWordLab.word value) = value := rfl

/-- Bridge for the production-to-`evalHOL` adapter: the exact HOL-shaped
    `holShapeOf` on the `HolValue` image `value.toHolValue` of a production
    value equals the production `panValueShape` (whose `StructContext` argument
    is vacuous).  Untagged: this is a Flapjack-specific adapter, not a HOL
    statement. -/
theorem holShapeOf_toHolValue {width : Nat} [NeZero width] (context : StructContext)
    (value : PanValue (BitVec width)) :
    holShapeOf value.toHolValue = panValueShape context value := by
  induction value using PanValue.toHolValue.induct with
  | case1 bits =>
      unfold PanValue.toHolValue holShapeOf panValueShape
      rfl
  | case2 fields ih =>
      unfold PanValue.toHolValue holShapeOf panValueShape
      rw [List.map_map]
      apply congrArg Shape.comb
      apply List.map_congr_left
      intro x hx
      exact ih x hx
  | case3 name fields ih =>
      unfold PanValue.toHolValue holShapeOf panValueShape
      rfl

/-- List lift of `holShapeOf_toHolValue`. -/
theorem holShapeOf_map_toHolValue {width : Nat} [NeZero width] (context : StructContext)
    (values : List (PanValue (BitVec width))) :
    (values.map PanValue.toHolValue).map holShapeOf = values.map (panValueShape context) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro value _
  exact holShapeOf_toHolValue context value

/-- Pointwise corollary: matching a shape against the HOL shape of
    `value.toHolValue` agrees with matching it against the production
    `panValueShape`. -/
theorem panShapeMatches_holShapeOf_toHolValue {width : Nat} [NeZero width] (context : StructContext)
    (shape : Shape) (value : PanValue (BitVec width)) :
    panShapeMatches shape (holShapeOf value.toHolValue) =
      panShapeMatches shape (panValueShape context value) := by
  rw [holShapeOf_toHolValue context value]

/-- Bridge for the production-to-`evalHOL` `NStruct` adapter: the field-shape
    predicate of `evalHOL` (over the `HolValue` image of the fields) agrees with
    the predicate used by the production `panValueFieldsExactHOL`.  Untagged: a
    Flapjack-specific adapter, not a HOL statement. -/
theorem panValueFieldsShapeHOL_eq {width : Nat} [NeZero width] (structs : StructContext)
    (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue (BitVec width))) :
    List.all
        ((expected.map Prod.snd).zip
          ((actual.map (fun pair => (pair.1, pair.2.toHolValue))).map Prod.snd))
        (fun pair => panShapeMatches pair.1 (holShapeOf pair.2))
      = List.all
        ((expected.map Prod.snd).zip (actual.map Prod.snd))
        (fun pair => panShapeMatches pair.1 (panValueShape structs pair.2)) := by
  induction expected generalizing actual with
  | nil => cases actual <;> rfl
  | cons head tail ih =>
      obtain ⟨expectedName, expectedShape⟩ := head
      cases actual with
      | nil => rfl
      | cons actualHead actualTail =>
          obtain ⟨actualName, actualValue⟩ := actualHead
          simp only [List.map_cons, List.zip_cons_cons, List.all_cons]
          rw [panShapeMatches_holShapeOf_toHolValue structs expectedShape actualValue,
            ih actualTail]

/-- Bridge for the production-to-`evalHOL` `NStruct` adapter: the whole
    production `panValueFieldsExactHOL` field check on `PanValue` fields equals
    the inline `evalHOL` predicate (propositional field-name equality decided to
    a `Bool` and the `HolValue`-image shape check).  Untagged: a Flapjack-specific
    adapter, not a HOL statement. -/
theorem panValueFieldsExactHOL_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (structs : StructContext) (info : StructInfo)
    (actual : List (FieldName × PanValue (BitVec width))) :
    panValueFieldsExactHOL structs info.fields actual =
      (decide (info.fields.map Prod.fst = actual.map Prod.fst) &&
        List.all
          ((info.fields.map Prod.snd).zip
            ((actual.map (fun pair => (pair.1, pair.2.toHolValue))).map Prod.snd))
          (fun pair => panShapeMatches pair.1 (holShapeOf pair.2))) := by
  unfold panValueFieldsExactHOL
  rw [← panValueFieldsShapeHOL_eq structs info.fields actual]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact beq_iff_eq

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): HOL `theValWord`
    (`cakeml/pancake/semantics/panSemScript.sml:39`) is a *partial* function
    (`theValWord (ValWord w) = w`, undefined otherwise); this Lean helper is the
    totalized version returning `0` on non-word values.  It is used only inside
    the `Op`/`Panop` clauses *after* the `EVERY isValWord` guard, where HOL's
    `case ... of ValWord n => n` is also total; it carries no `@[hol]` tag.
    An exact port would have to leave the non-`ValWord` branch unspecified as
    HOL's `theValWord` does, over the exact positive-width `ValueHOL` carrier;
    faithful-port dependency `flapjack-0lj.5` (with carrier umbrella
    `flapjack-pxn.18.3.5.8`). -/
def holValueWord {width : Nat} : HolValue width → RiscV.Word width
  | .val (.word value) => value
  | _ => 0

/-- Exact width-indexed port of HOL `pan_op_def`
    (`cakeml/pancake/semantics/panSemScript.sml:191`): only `Mul` on exactly two
    word operands is defined.  Carries `[NeZero width]` because HOL word types
    have positive `dimindex`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "pan_op_def"]
def panOpHOL {width : Nat} [NeZero width] (operator : PanOp) (values : List (RiscV.Word width)) :
    Option (RiscV.Word width) :=
  match operator, values with
  | .mul, [left, right] => some (left * right)
  | _, _ => none

/-- HOL-shaped source state for `panSem$eval_def`
    (`cakeml/pancake/semantics/panSemScript.sml:44-62`).  The fields are the
    source state components; `memaddrs`/`shMemaddrs` render the HOL word sets
    as predicates. -/
structure PanSemHolState (width : Nat) (σ : Type) where
  locals : VarName → Option (HolValue width)
  globals : VarName → Option (HolValue width)
  structs : StructContextHOL
  code : FunName → Option (List (VarName × Shape) × Prog (BitVec width) × Shape)
  eshapes : ExceptionId → Option Shape
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : FfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port): clause-for-clause the
   same as HOL `panSem$eval_def`, but the carrier `PanSemHolState` stores
   `locals`/`globals`/`code`/`eshapes` keyed by `VarName`/`FunName`/`ExceptionId`
   = `String` and holds String-bearing `HolValue`, whereas HOL
   `varname`/`funname`/`eid`/`stcname`/`fldname` are `mlstring`.  The `@[hol]`
   tag is therefore withheld (bead `flapjack-0lj`); the exact MlString-keyed
   evaluator is tracked by `flapjack-pxn.18.3.5.8`.  HOL quantifies over
   `'a word`; Lean represents that polymorphic width by `BitVec width`
   (`RiscV.Word width`) with `[NeZero width]` (HOL `dimindex(:'a)` is nonzero). -/
mutual
  def evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
      (state : PanSemHolState width σ)
      [DecidablePred state.memaddrs] : Exp (BitVec width) → Option (HolValue width)
    | .const value => some (.val (.word value))
    | .var .local name => state.locals name
    | .var .global name => state.globals name
    | .rStruct fields => (evalListHOL state fields).map HolValue.rStruct
    | .rField index value =>
        match evalHOL state value with
        | some (.rStruct values) => values[index]?
        | _ => none
    | .nStruct name fields =>
        match lookupInfo name state.structs with
        | none => none
        | some info =>
            if info.fields.map Prod.fst = fields.map Prod.fst then
              match evalFieldsHOL state fields with
              | none => none
              | some fieldValues =>
                  if ((info.fields.map Prod.snd).zip (fieldValues.map Prod.snd)).all
                        (fun pair => panShapeMatches pair.1 (holShapeOf pair.2)) then
                    some (.nStruct name fieldValues)
                  else none
            else none
    | .nField name value =>
        match evalHOL state value with
        | some (.nStruct structName values) =>
            if (lookupInfo structName state.structs).isSome then
              lookupInfo name values
            else none
        | _ => none
    | .load shape address =>
        if isWfShapeHOL state.structs shape then
          match evalHOL state address with
          | some (.val (.word word)) =>
              panMemLoadHOL shape word state.memaddrs state.memory state.structs
          | _ => none
        else none
    | .load32 address =>
        match evalHOL state address with
        | some (.val (.word word)) =>
            (panMemLoad32HOL state.memory state.memaddrs state.be word).map
              (fun value => .val (.word (BitVec.ofNat width value.toNat)))
        | _ => none
    | .loadByte address =>
        match evalHOL state address with
        | some (.val (.word word)) =>
            (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
              (fun byte => .val (.word (BitVec.ofNat width byte.toNat)))
        | _ => none
    | .op operator args =>
        match evalListHOL state args with
        | none => none
        | some values =>
            if values.all holValueIsWord then
              (wordOpHOL operator (values.map holValueWord)).map
                (fun word => .val (.word word))
            else none
    | .panOp operator args =>
        match evalListHOL state args with
        | none => none
        | some values =>
            if values.all holValueIsWord then
              (panOpHOL operator (values.map holValueWord)).map
                (fun word => .val (.word word))
            else none
    | .cmp operator left right =>
        match evalHOL state left, evalHOL state right with
        | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
            some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL operator leftWord rightWord then 1 else 0)))
        | _, _ => none
    | .shift operator left right =>
        match evalHOL state left, evalHOL state right with
        | some (.val (.word leftWord)), some (.val (.word rightWord)) =>
            (wordShiftHOL operator leftWord rightWord.toNat).map
              (fun word => .val (.word word))
        | _, _ => none
    | .baseAddr => some (.val (.word state.baseAddr))
    | .topAddr => some (.val (.word state.topAddr))
    | .bytesInWord => some (.val (.word (panBytesInWord width)))
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial | omega

  def evalListHOL {width : Nat} [NeZero width] [LawfulBEq String]
      (state : PanSemHolState width σ)
      [DecidablePred state.memaddrs] :
      List (Exp (BitVec width)) → Option (List (HolValue width))
    | [] => some []
    | expression :: expressions =>
        match evalHOL state expression, evalListHOL state expressions with
        | some value, some values => some (value :: values)
        | _, _ => none
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial | omega

  def evalFieldsHOL {width : Nat} [NeZero width] [LawfulBEq String]
      (state : PanSemHolState width σ)
      [DecidablePred state.memaddrs] :
      List (FieldName × Exp (BitVec width)) → Option (List (FieldName × HolValue width))
    | [] => some []
    | pair :: rest =>
        match evalHOL state pair.2, evalFieldsHOL state rest with
        | some value, some values => some ((pair.1, value) :: values)
        | _, _ => none
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals
      simp_wf
      first
      | (have : sizeOf pair.2 < sizeOf pair := by cases pair; simp +arith
         omega)
      | omega
end

/-! ## Modular production-to-`evalHOL` bridge (flapjack-pxn.18.3.6.9.2)

The production `evalPanValueExp` family (`Flapjack/PanValues.lean`) and the exact
tagged `evalHOL` family share the same recursive structure.  These untagged
lemmas record the list/field halves of the bridge: assuming the per-expression
agreement `evalPanValueExp … e = (evalHOL state e).map HolValue.toPanValue` for
the elements under consideration, the production list/field recursion agrees
with `evalListHOL`/`evalFieldsHOL` after mapping `HolValue.toPanValue`.  They are
the reusable pieces of the full production adapter tracked by bead
`flapjack-pxn.18.3.6.9.2`; the remaining work is discharging the per-expression
hypothesis for every expression constructor (state projection and memory
codec). -/

theorem evalPanValueExps_eq_evalListHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (expressions : List (Exp (RiscV.Word width)))
    (hexp : ∀ expression ∈ expressions,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          expression (memoryAccess := access)
        = (evalHOL state expression).map HolValue.toPanValue) :
    evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord expressions (memoryAccess := access)
      = (evalListHOL state expressions).map (List.map HolValue.toPanValue) := by
  induction expressions with
  | nil => simp [evalPanValueExp.evalPanValueExps, evalListHOL]
  | cons expression expressions ih =>
      have hhead := hexp expression List.mem_cons_self
      have htail : ∀ e ∈ expressions, evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord e (memoryAccess := access)
          = (evalHOL state e).map HolValue.toPanValue :=
        fun e he => hexp e (List.mem_cons_of_mem expression he)
      rw [evalPanValueExp.evalPanValueExps]
      cases h1 : evalHOL state expression with
      | none =>
          rw [h1] at hhead
          simp only [Option.map_none] at hhead
          rw [hhead]
          simp [evalListHOL, h1]
      | some value =>
          rw [h1] at hhead
          simp only [Option.map_some] at hhead
          rw [hhead, ih htail]
          cases h2 : evalListHOL state expressions <;>
            simp_all [evalListHOL, Option.bind_some]

theorem evalPanValueFields_eq_evalFieldsHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (fields : List (FieldName × Exp (RiscV.Word width)))
    (hexp : ∀ pair ∈ fields,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          pair.2 (memoryAccess := access)
        = (evalHOL state pair.2).map HolValue.toPanValue) :
    evalPanValueExp.evalPanValueFields structs locals globals memory baseAddress topAddress
        bytesInWord fields (memoryAccess := access)
      = (evalFieldsHOL state fields).map
          (List.map (fun pair => (pair.1, HolValue.toPanValue pair.2))) := by
  induction fields with
  | nil => simp [evalPanValueExp.evalPanValueFields, evalFieldsHOL]
  | cons pair rest ih =>
      obtain ⟨name, expression⟩ := pair
      have hhead := hexp (name, expression) List.mem_cons_self
      have htail : ∀ p ∈ rest, evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord p.2 (memoryAccess := access)
          = (evalHOL state p.2).map HolValue.toPanValue :=
        fun p hp => hexp p (List.mem_cons_of_mem (name, expression) hp)
      rw [evalPanValueExp.evalPanValueFields]
      cases h1 : evalHOL state expression with
      | none =>
          rw [h1] at hhead
          simp only [Option.map_none] at hhead
          rw [hhead]
          simp [evalFieldsHOL, h1]
      | some value =>
          rw [h1] at hhead
          simp only [Option.map_some] at hhead
          rw [hhead, ih htail]
          cases h2 : evalFieldsHOL state rest <;>
            simp_all [evalFieldsHOL, Option.bind_some]

/-- The `Const` clause of the exact tagged `evalHOL` agrees with the production
`evalPanValueExp` (a single fully-closed instance of the per-expression
hypothesis used by the modular bridges above). -/
theorem evalPanValueExp_const_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width))) (value : RiscV.Word width) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.const value) (memoryAccess := access)
      = (evalHOL state (.const value)).map HolValue.toPanValue := by
  simp [evalPanValueExp, evalHOL, HolValue.toPanValue_val]

/-- `.var .local` clause bridge: under a pointwise local-environment agreement, the
production lookup agrees with tagged `evalHOL` on the `HolValue` image. -/
theorem evalPanValueExp_var_local_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width))) (name : VarName)
    (hlocals : ∀ name, locals name = (state.locals name).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.var .local name) (memoryAccess := access)
      = (evalHOL state (.var .local name)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  exact hlocals name

/-- `.var .global` clause bridge (counterpart of `evalPanValueExp_var_local_eq_evalHOL`). -/
theorem evalPanValueExp_var_global_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width))) (name : VarName)
    (hglobals : ∀ name, globals name = (state.globals name).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.var .global name) (memoryAccess := access)
      = (evalHOL state (.var .global name)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  exact hglobals name

/-- `.baseAddr` clause bridge: production `baseAddress` agrees with `state.baseAddr`. -/
theorem evalPanValueExp_baseAddr_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (hbase : baseAddress = state.baseAddr) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .baseAddr (memoryAccess := access)
      = (evalHOL state .baseAddr).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL, hbase, Option.map_some, HolValue.toPanValue_val]

/-- `.topAddr` clause bridge: production `topAddress` agrees with `state.topAddr`. -/
theorem evalPanValueExp_topAddr_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (htop : topAddress = state.topAddr) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .topAddr (memoryAccess := access)
      = (evalHOL state .topAddr).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL, htop, Option.map_some, HolValue.toPanValue_val]

/-- `.bytesInWord` clause bridge: production `bytesInWord` agrees with the canonical
`panBytesInWord width`. -/
theorem evalPanValueExp_bytesInWord_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (hbytes : bytesInWord = panBytesInWord width) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .bytesInWord (memoryAccess := access)
      = (evalHOL state .bytesInWord).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL, hbytes, Option.map_some, HolValue.toPanValue_val]

/-- `.rStruct` clause bridge: under per-element production agreement on the field
expressions, production `.rStruct` agrees with tagged `evalHOL`. -/
theorem evalPanValueExp_rStruct_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (fields : List (Exp (RiscV.Word width)))
    (hfields : ∀ expression ∈ fields,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          expression (memoryAccess := access)
        = (evalHOL state expression).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.rStruct fields) (memoryAccess := access)
      = (evalHOL state (.rStruct fields)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [evalPanValueExps_eq_evalListHOL state structs locals globals memory baseAddress
    topAddress bytesInWord access fields hfields]
  rw [Option.map_map, Option.map_map]
  congr 1
  funext value
  rw [Function.comp_apply, Function.comp_apply, HolValue.toPanValue_rStruct]

/-- `.rField` clause bridge: under production agreement on the structure expression,
production `.rField` agrees with tagged `evalHOL` (both project the index of a
`RStruct` value and fail otherwise). -/
theorem evalPanValueExp_rField_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (index : Nat) (value : Exp (RiscV.Word width))
    (hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        value (memoryAccess := access)
      = (evalHOL state value).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.rField index value) (memoryAccess := access)
      = (evalHOL state (.rField index value)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [hvalue]
  cases hv : evalHOL state value with
  | none => simp
  | some holValue =>
      cases holValue with
      | val word => cases word with | word bits => simp [HolValue.toPanValue_val]
      | rStruct values => simp [HolValue.toPanValue_rStruct, List.getElem?_map]
      | nStruct name fields => simp [HolValue.toPanValue_nStruct]

/-! ### `nStruct`/`nField` clause bridges (flapjack-pxn.18.3.6.9.2.8) -/

/-- `HolValue.toPanValue` undoes `PanValue.toHolValue` on field lists. -/
theorem map_toPanValue_toHolValue {width : Nat} (fieldValues : List (FieldName × HolValue width)) :
    (fieldValues.map (fun pair => (pair.1, HolValue.toPanValue pair.2))).map
        (fun pair => (pair.1, pair.2.toHolValue)) = fieldValues := by
  rw [List.map_map]
  have hcong :
      List.map ((fun pair => (pair.fst, pair.snd.toHolValue)) ∘
        fun pair => (pair.fst, pair.snd.toPanValue)) fieldValues = List.map id fieldValues := by
    apply List.map_congr_left
    intro pair _
    obtain ⟨name, value⟩ := pair
    simp [Function.comp_apply, HolValue.toPanValue_toHolValue]
  rw [hcong]
  simp

/-- `lookupPanValueField` over the `toPanValue` image is `lookupInfo` mapped by
`HolValue.toPanValue`. -/
theorem lookupPanValueField_map_toPanValue {width : Nat} [LawfulBEq String] (name : FieldName)
    (fields : List (FieldName × HolValue width)) :
    lookupPanValueField name (fields.map (fun pair => (pair.1, HolValue.toPanValue pair.2))) =
      (lookupInfo name fields).map HolValue.toPanValue := by
  induction fields with
  | nil => simp [lookupPanValueField, lookupInfo]
  | cons head rest ih =>
      obtain ⟨n, v⟩ := head
      by_cases h : n == name <;> simp [lookupPanValueField, lookupInfo, h, ih]

/-- Evaluating a field list preserves the field names. -/
theorem evalFieldsHOL_fieldNames {width : Nat} [NeZero width] [LawfulBEq String]
    {state : PanSemHolState width σ} [DecidablePred state.memaddrs]
    {fields : List (FieldName × Exp (RiscV.Word width))}
    {fieldValues : List (FieldName × HolValue width)}
    (h : evalFieldsHOL state fields = some fieldValues) :
    fieldValues.map Prod.fst = fields.map Prod.fst := by
  induction fields generalizing fieldValues with
  | nil => simp [evalFieldsHOL] at h; subst h; simp
  | cons head rest ih =>
      obtain ⟨name, expression⟩ := head
      cases hv : evalHOL state expression with
      | none => rw [evalFieldsHOL, hv] at h; simp at h
      | some value =>
          cases hr : evalFieldsHOL state rest with
          | none => rw [evalFieldsHOL, hv, hr] at h; simp at h
          | some restValues =>
              rw [evalFieldsHOL, hv, hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simpa using ih hr

/-- `.nStruct` clause bridge: under production agreement on the field expressions and
the state/struct-context relation `state.structs = structs.toHOL`, production
`.nStruct` agrees with tagged `evalHOL`. -/
theorem evalPanValueExp_nStruct_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (name : StructName) (fields : List (FieldName × Exp (RiscV.Word width)))
    (hstructs : state.structs = structs.toHOL)
    (hfields : ∀ pair ∈ fields,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          pair.2 (memoryAccess := access)
        = (evalHOL state pair.2).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.nStruct name fields) (memoryAccess := access)
      = (evalHOL state (.nStruct name fields)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [hstructs, lookupInfo_toHOL]
  cases hlook : lookupInfo name structs with
  | none => simp
  | some info =>
      simp only [Option.map_some]
      rw [evalPanValueFields_eq_evalFieldsHOL state structs locals globals memory
        baseAddress topAddress bytesInWord access fields hfields]
      cases hfv : evalFieldsHOL state fields with
      | none => simp
      | some fieldValues =>
          simp
          rw [panValueFieldsExactHOL_eq_evalHOL structs info
            (fieldValues.map (fun pair => (pair.1, HolValue.toPanValue pair.2)))]
          rw [map_toPanValue_toHolValue fieldValues]
          have hname := evalFieldsHOL_fieldNames hfv
          have hfst : List.map Prod.fst
              (List.map (fun pair => (pair.1, HolValue.toPanValue pair.2)) fieldValues) =
              List.map Prod.fst fields := by
            rw [List.map_map]
            have hcomp : (Prod.fst ∘ fun pair : FieldName × HolValue width =>
                (pair.1, HolValue.toPanValue pair.2)) =
                (Prod.fst : FieldName × HolValue width → FieldName) := by
              funext pair
              rfl
            rw [hcomp]
            exact hname
          rw [hfst]
          by_cases hfn : info.fields.map Prod.fst = fields.map Prod.fst
          · simp only [hfn, decide_true, Bool.true_and]
            by_cases hall : List.all
                ((info.fields.map Prod.snd).zip (fieldValues.map Prod.snd))
                (fun pair => panShapeMatches pair.1 (holShapeOf pair.2)) = true
            · simp [hall, HolValue.toPanValue_nStruct]
            · simp [hall]
          · simp [hfn]

/-- `.nField` clause bridge: under production agreement on the structure expression and
the state/struct-context relation, production `.nField` agrees with tagged `evalHOL`. -/
theorem evalPanValueExp_nField_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (RiscV.Word width)))
    (memory : RiscV.Word width → Option (PanValue (RiscV.Word width)))
    (baseAddress topAddress bytesInWord : RiscV.Word width)
    (access : Option (PanValueMemoryAccess (RiscV.Word width)))
    (name : FieldName) (value : Exp (RiscV.Word width))
    (hstructs : state.structs = structs.toHOL)
    (hvalue : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        value (memoryAccess := access)
      = (evalHOL state value).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.nField name value) (memoryAccess := access)
      = (evalHOL state (.nField name value)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [hvalue, hstructs]
  cases hv : evalHOL state value with
  | none => simp
  | some holValue =>
      cases holValue with
      | val word => cases word with | word bits => simp [HolValue.toPanValue_val]
      | rStruct values => simp [HolValue.toPanValue_rStruct]
      | nStruct structName values =>
          cases hs : lookupInfo structName structs with
          | none => simp [hs, lookupInfo_toHOL_isSome, HolValue.toPanValue_nStruct]
          | some info =>
              simp [hs, lookupInfo_toHOL_isSome, lookupPanValueField_map_toPanValue name values,
                HolValue.toPanValue_nStruct]

/-! ### `.op` clause bridge to `evalHOL` (flapjack-pxn.18.3.6.9.2.9) -/

theorem panValueWordProjection_toPanValue {width : Nat} [NeZero width] (value : HolValue width) :
    panValueWordProjection value.toPanValue =
      (if holValueIsWord value then some (holValueWord value) else none) := by
  cases value with
  | val word => cases word with
    | word bits => simp [HolValue.toPanValue_val, holValueIsWord, holValueWord]
  | rStruct fields => simp [HolValue.toPanValue_rStruct, holValueIsWord]
  | nStruct name fields => simp [HolValue.toPanValue_nStruct, holValueIsWord]

theorem mapM_panValueWordProjection_toPanValue {width : Nat} [NeZero width]
    (values : List (HolValue width)) :
    (values.map HolValue.toPanValue).mapM panValueWordProjection =
      (if values.all holValueIsWord then some (values.map holValueWord) else none) := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.mapM_cons, List.all_cons]
      rw [panValueWordProjection_toPanValue value]
      cases hw : holValueIsWord value with
      | false => simp
      | true =>
          cases hr : rest.all holValueIsWord with
          | false => simp [hr, ih]
          | true => simp [hr, ih]

theorem evalPanValueExp_op_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : PanValueMemoryAccess (BitVec width))
    (operator : BinOp) (arguments : List (Exp (BitVec width)))
    (hargs : ∀ e ∈ arguments,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
        (memoryAccess := some access) = (evalHOL state e).map HolValue.toPanValue)
    (hwordOp : ∀ (op : BinOp) (values : List (BitVec width)),
      access.wordOp op values = wordOpHOL op values) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.op operator arguments) (memoryAccess := some access)
      = (evalHOL state (.op operator arguments)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [evalPanValueExps_eq_evalListHOL state structs locals globals memory baseAddress
    topAddress bytesInWord (some access) arguments hargs]
  cases hlist : evalListHOL state arguments with
  | none => simp
  | some hvs =>
      change Option.bind (some (List.map HolValue.toPanValue hvs))
          (fun values => Option.bind (List.mapM panValueWordProjection values)
            (fun values => Option.map PanValue.word (access.wordOp operator values)))
        = Option.map HolValue.toPanValue
            (if hvs.all holValueIsWord = true then
              Option.map (fun word => HolValue.val (HolWordLab.word word))
                (wordOpHOL operator (List.map holValueWord hvs))
            else none)
      rw [Option.bind_some]
      by_cases hall : hvs.all holValueIsWord = true
      · rw [mapM_panValueWordProjection_toPanValue hvs]
        simp only [if_pos hall]
        rw [Option.bind_some]
        rw [hwordOp]
        change Option.map PanValue.word (wordOpHOL operator (hvs.map holValueWord))
          = Option.map HolValue.toPanValue
              (Option.map (fun word => HolValue.val (HolWordLab.word word))
                (wordOpHOL operator (hvs.map holValueWord)))
        rw [Option.map_map]
        congr 1
        funext word
        exact (HolValue.toPanValue_val word).symm
      · rw [mapM_panValueWordProjection_toPanValue hvs]
        simp only [if_neg hall]
        simp

/-! ## Production `panOp` clause bridge (flapjack-pxn.18.3.6.9.2.10)

Untagged production-to-evalHOL bridge for the `.panOp` expression clause. The
executed clause destructures the evaluated value list as exactly two words and
calls `evalPanOp`; the tagged `evalHOL` instead checks `List.all holValueIsWord`
and calls `panOpHOL`. The two agree because `evalPanOp` is definitionally
`panOpHOL`. No new `@[hol]` tags are added here. -/

theorem evalPanOp_eq_panOpHOL {width : Nat} [NeZero width] (operator : PanOp)
    (values : List (RiscV.Word width)) :
    evalPanOp operator values = panOpHOL (width := width) operator values := by
  cases operator <;>
    (cases values with
     | nil => rfl
     | cons x xs =>
         cases xs with
         | nil => rfl
         | cons y ys =>
             cases ys with
             | nil => rfl
             | cons z zs => rfl)

theorem panOpHOL_nil {width : Nat} [NeZero width] (operator : PanOp) :
    panOpHOL (width := width) operator [] = none := by
  cases operator <;> rfl

theorem panOpHOL_one {width : Nat} [NeZero width] (operator : PanOp)
    (x : RiscV.Word width) :
    panOpHOL (width := width) operator [x] = none := by
  cases operator <;> rfl

theorem panOpHOL_three {width : Nat} [NeZero width] (operator : PanOp)
    (x y z : RiscV.Word width) (rest : List (RiscV.Word width)) :
    panOpHOL (width := width) operator (x :: y :: z :: rest) = none := by
  cases operator <;> rfl

theorem evalPanValueExp_panOp_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : Option (PanValueMemoryAccess (BitVec width)))
    (operator : PanOp) (arguments : List (Exp (BitVec width)))
    (hargs : ∀ e ∈ arguments,
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
        (memoryAccess := access) = (evalHOL state e).map HolValue.toPanValue) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.panOp operator arguments) (memoryAccess := access)
      = (evalHOL state (.panOp operator arguments)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [evalPanValueExps_eq_evalListHOL state structs locals globals memory baseAddress
    topAddress bytesInWord access arguments hargs]
  cases hlist : evalListHOL state arguments with
  | none => simp
  | some hvs =>
      cases hvs with
      | nil => simp [panOpHOL_nil]
      | cons a as =>
          cases as with
          | nil =>
              cases a with
              | val w =>
                  cases w with
                  | word aBits => simp [holValueIsWord, panOpHOL_one]
              | rStruct f => simp [holValueIsWord, HolValue.toPanValue_rStruct]
              | nStruct n f => simp [holValueIsWord, HolValue.toPanValue_nStruct]
          | cons b bs =>
              cases bs with
              | nil =>
                  cases a with
                  | val w =>
                      cases w with
                      | word aBits =>
                          cases b with
                          | val w2 =>
                              cases w2 with
                              | word bBits =>
                                  simp only [List.map_cons, List.map_nil,
                                    HolValue.toPanValue_val, List.all_cons, List.all_nil,
                                    holValueIsWord, Bool.true_and, if_true, holValueWord,
                                    Option.map_some]
                                  simp
                                  rw [show (HolValue.toPanValue ∘
                                        fun (w : RiscV.Word width) => HolValue.val (HolWordLab.word w))
                                      = (fun w => PanValue.word w) from by
                                    funext w
                                    exact HolValue.toPanValue_val w]
                                  exact congrArg (Option.map PanValue.word)
                                    (evalPanOp_eq_panOpHOL (width := width) operator [aBits, bBits])
                          | rStruct f =>
                              simp [holValueIsWord, HolValue.toPanValue_rStruct]
                          | nStruct n f =>
                              simp [holValueIsWord, HolValue.toPanValue_nStruct]
                  | rStruct f =>
                      cases b <;> simp [holValueIsWord, HolValue.toPanValue_rStruct]
                  | nStruct n f =>
                      cases b <;> simp [holValueIsWord, HolValue.toPanValue_nStruct]
              | cons c cs =>
                  cases a <;> cases b <;> cases c <;>
                    simp [holValueIsWord, panOpHOL_three]

section

attribute [local simp] HolValue.toPanValue_val HolValue.toPanValue_rStruct HolValue.toPanValue_nStruct

theorem evalPanValueExp_cmp_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : PanValueMemoryAccess (BitVec width))
    (operator : Cmp) (left right : Exp (BitVec width))
    (hleft : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        left (memoryAccess := some access) = (evalHOL state left).map HolValue.toPanValue)
    (hright : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        right (memoryAccess := some access) = (evalHOL state right).map HolValue.toPanValue)
    (hcmp : ∀ (op : Cmp) (l r : BitVec width),
      access.compare op l r =
        (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op l r then 1 else 0)) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.cmp operator left right) (memoryAccess := some access)
      = (evalHOL state (.cmp operator left right)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [hleft, hright]
  cases hl : evalHOL state left with
  | none => simp
  | some lv =>
      cases hr : evalHOL state right with
      | none => simp
      | some rv =>
          cases lv with
          | val w =>
              cases w with
              | word lw =>
                  cases rv with
                  | val w2 =>
                      cases w2 with
                      | word rw => simp [hcmp]
                  | rStruct f => simp
                  | nStruct n f => simp
          | rStruct f =>
              cases rv with
              | val w2 =>
                  cases w2 with
                  | word rw => simp
              | rStruct f => simp
              | nStruct n f => simp
          | nStruct n f =>
              cases rv with
              | val w2 =>
                  cases w2 with
                  | word rw => simp
              | rStruct f => simp
              | nStruct n f => simp

theorem evalPanValueExp_shift_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : PanValueMemoryAccess (BitVec width))
    (operator : Shift) (left right : Exp (BitVec width))
    (hleft : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        left (memoryAccess := some access) = (evalHOL state left).map HolValue.toPanValue)
    (hright : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        right (memoryAccess := some access) = (evalHOL state right).map HolValue.toPanValue)
    (hshift : ∀ (op : Shift) (l r : BitVec width),
      access.shift op l r = wordShiftHOL op l r.toNat) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.shift operator left right) (memoryAccess := some access)
      = (evalHOL state (.shift operator left right)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [hleft, hright]
  cases hl : evalHOL state left with
  | none => simp
  | some lv =>
      cases hr : evalHOL state right with
      | none => simp
      | some rv =>
          cases lv with
          | val w =>
              cases w with
              | word lw =>
                  cases rv with
                  | val w2 =>
                      cases w2 with
                      | word rw =>
                          simp [hshift]
                          rw [show (HolValue.toPanValue ∘ fun word => HolValue.val (HolWordLab.word word))
                              = (fun word => PanValue.word word) from by
                                funext word
                                exact HolValue.toPanValue_val word]
                  | rStruct f => simp
                  | nStruct n f => simp
          | rStruct f =>
              cases rv with
              | val w2 =>
                  cases w2 with
                  | word rw => simp
              | rStruct f => simp
              | nStruct n f => simp
          | nStruct n f =>
              cases rv with
              | val w2 =>
                  cases w2 with
                  | word rw => simp
              | rStruct f => simp
              | nStruct n f => simp

theorem evalPanValueExp_load32_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : PanValueMemoryAccess (BitVec width))
    (address : Exp (BitVec width))
    (haddress : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        address (memoryAccess := some access) = (evalHOL state address).map HolValue.toPanValue)
    (hread : ∀ (word : BitVec width),
      (access.read32 access.domain memory bytesInWord word).map PanValue.word
        = (panMemLoad32HOL state.memory state.memaddrs state.be word).map
            (fun value => PanValue.word (BitVec.ofNat width value.toNat))) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.load32 address) (memoryAccess := some access)
      = (evalHOL state (.load32 address)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [haddress]
  cases ha : evalHOL state address with
  | none => simp
  | some hv =>
      cases hv with
      | val w =>
          cases w with
          | word bits =>
              simp only [Option.map_some]
              rw [HolValue.toPanValue_val bits]
              change Option.map PanValue.word (access.read32 access.domain memory bytesInWord bits)
                = Option.map HolValue.toPanValue
                    (Option.map (fun (value : RiscV.Word 32) =>
                        HolValue.val (HolWordLab.word (BitVec.ofNat width value.toNat)))
                      (panMemLoad32HOL state.memory state.memaddrs state.be bits))
              rw [hread bits]
              rw [Option.map_map]
              congr 1
              funext value
              rw [Function.comp_apply]
              exact (HolValue.toPanValue_val (BitVec.ofNat width value.toNat)).symm
      | rStruct f => simp
      | nStruct n f => simp

theorem evalPanValueExp_loadByte_eq_evalHOL {width : Nat} [NeZero width] [LawfulBEq String]
    (state : PanSemHolState width σ) [DecidablePred state.memaddrs]
    (structs : StructContext) (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : PanValueMemoryAccess (BitVec width))
    (address : Exp (BitVec width))
    (haddress : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        address (memoryAccess := some access) = (evalHOL state address).map HolValue.toPanValue)
    (hread : ∀ (word : BitVec width),
      (access.readByte access.domain memory bytesInWord word).map PanValue.word
        = (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
            (fun byte => PanValue.word (BitVec.ofNat width byte.toNat))) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.loadByte address) (memoryAccess := some access)
      = (evalHOL state (.loadByte address)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [haddress]
  cases ha : evalHOL state address with
  | none => simp
  | some hv =>
      cases hv with
      | val w =>
          cases w with
          | word bits =>
              simp only [Option.map_some]
              rw [HolValue.toPanValue_val bits]
              change Option.map PanValue.word (access.readByte access.domain memory bytesInWord bits)
                = Option.map HolValue.toPanValue
                    (Option.map (fun (byte : UInt8) =>
                        HolValue.val (HolWordLab.word (BitVec.ofNat width byte.toNat)))
                      (panMemLoadByteHOL state.memory state.memaddrs state.be bits))
              rw [hread bits]
              rw [Option.map_map]
              congr 1
              funext value
              rw [Function.comp_apply]
              exact (HolValue.toPanValue_val (BitVec.ofNat width value.toNat)).symm
      | rStruct f => simp
      | nStruct n f => simp

/-! ## Production structured `.load` clause bridge (flapjack-pxn.18.3.6.9.2.13)

Width-64 executed-path bridge: production `evalPanValueExp (.load shape address)`
under `some (panSemBitVec64MemoryAccess execState)` agrees with tagged `evalHOL`
once the exact source state's `structs`/`memory`/`memaddrs` are related to the
production `StructContext`/memory/`panValueFlatMachineDomain` and the guard holds.
Reuses the capstone `panValueFlatLoad_eq_panMemLoadHOL`.  Untagged production-side
adapter. -/

theorem evalPanValueExp_load_eq_evalHOL {σ ffi : Type} [LawfulBEq String]
    (state : PanSemHolState 64 σ) [DecidablePred state.memaddrs]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (shape : Shape) (address : Exp (RiscV.Word 64))
    (haddress : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        address (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL state address).map HolValue.toPanValue)
    (hstructs : state.structs = structs.toHOL)
    (hmem : state.memory = panValueWordHOL memory)
    (hdom : state.memaddrs = panValueFlatMachineDomain execState memory)
    (hbytes : bytesInWord = panSemBitVec64BytesInWord)
    (hwf : isWfShape structs shape = true) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.load shape address) (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL state (.load shape address)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [haddress, hstructs, isWfShapeHOL_toHOL structs shape, hwf]
  cases ha : evalHOL state address with
  | none => simp
  | some hv =>
      cases hv with
      | val w =>
          cases w with
          | word bits =>
              simp only [Option.map_some]
              rw [HolValue.toPanValue_val bits]
              simp only [hbytes]
              simp
              rw [panValueFlatLoad_eq_panMemLoadHOL execState memory structs shape bits hwf]
              simp only [hmem, hdom]
      | rStruct fs => simp only [Option.map_some]; rw [HolValue.toPanValue_rStruct]; simp
      | nStruct nm fs => simp only [Option.map_some]; rw [HolValue.toPanValue_nStruct]; simp

/-- Full `.load` clause bridge for an arbitrary `Shape`: unlike
`evalPanValueExp_load_eq_evalHOL`, this needs no `isWfShape structs shape = true`
side condition.  Both the well-formed branch (via the capstone
`panValueFlatLoad_eq_panMemLoadHOL`) and the ill-formed branch (where
`panValueFlatLoad` and the tagged `isWfShapeHOL` guard both collapse to failure)
are handled.  Untagged production-side adapter. -/
theorem evalPanValueExp_load_eq_evalHOL_anyShape {σ ffi : Type} [LawfulBEq String]
    (state : PanSemHolState 64 σ) [DecidablePred state.memaddrs]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (shape : Shape) (address : Exp (RiscV.Word 64))
    (haddress : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        address (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL state address).map HolValue.toPanValue)
    (hstructs : state.structs = structs.toHOL)
    (hmem : state.memory = panValueWordHOL memory)
    (hdom : state.memaddrs = panValueFlatMachineDomain execState memory)
    (hbytes : bytesInWord = panSemBitVec64BytesInWord) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.load shape address) (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL state (.load shape address)).map HolValue.toPanValue := by
  simp only [evalPanValueExp, evalHOL]
  rw [haddress, hstructs, isWfShapeHOL_toHOL structs shape]
  by_cases hwf : isWfShape structs shape = true
  · rw [hwf]
    cases ha : evalHOL state address with
    | none => simp
    | some hv =>
        cases hv with
        | val w =>
            cases w with
            | word bits =>
                simp only [Option.map_some]
                rw [HolValue.toPanValue_val bits]
                simp only [hbytes]
                simp
                rw [panValueFlatLoad_eq_panMemLoadHOL execState memory structs shape bits hwf]
                simp only [hmem, hdom]
        | rStruct fs => simp only [Option.map_some]; rw [HolValue.toPanValue_rStruct]; simp
        | nStruct nm fs => simp only [Option.map_some]; rw [HolValue.toPanValue_nStruct]; simp
  · have hwf' : isWfShape structs shape = false := by
      cases h : isWfShape structs shape <;> simp_all
    rw [hwf']
    cases ha : evalHOL state address with
    | none => simp
    | some hv =>
        cases hv with
        | val w =>
            cases w with
            | word bits =>
                simp only [Option.map_some]
                rw [HolValue.toPanValue_val bits]
                simp [panValueFlatLoad, hwf']
        | rStruct fs => simp only [Option.map_some]; rw [HolValue.toPanValue_rStruct]; simp
        | nStruct nm fs => simp only [Option.map_some]; rw [HolValue.toPanValue_nStruct]; simp

 /-- Bundled hypotheses for the whole-expression production-to-`evalHOL` adapter: the
    exact source state's `structs`/`memory`/`memaddrs` related to the production
    `StructContext`/memory/`panValueFlatMachineDomain`, the environment/base/top/bytes
    projections, and the executed access's `wordOp`/compare/shift/read32/readByte
    codecs.  Untagged production-side adapter bundle. -/
structure PanValueEvalRel {σ ffi : Type} (state : PanSemHolState 64 σ)
    [DecidablePred state.memaddrs]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64) : Prop where
  hstructs : state.structs = structs.toHOL
  hmem : state.memory = panValueWordHOL memory
  hdom : state.memaddrs = panValueFlatMachineDomain execState memory
  hlocals : ∀ name, locals name = (state.locals name).map HolValue.toPanValue
  hglobals : ∀ name, globals name = (state.globals name).map HolValue.toPanValue
  hbase : baseAddress = state.baseAddr
  htop : topAddress = state.topAddr
  hbytes : bytesInWord = panSemBitVec64BytesInWord
  hwordOp : ∀ (op : BinOp) (values : List (RiscV.Word 64)),
    (panSemBitVec64MemoryAccess execState).wordOp op values = wordOpHOL op values
  hcmp : ∀ (op : Cmp) (l r : RiscV.Word 64),
    (panSemBitVec64MemoryAccess execState).compare op l r =
      (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op l r then 1 else 0)
  hshift : ∀ (op : Shift) (l r : RiscV.Word 64),
    (panSemBitVec64MemoryAccess execState).shift op l r = wordShiftHOL op l r.toNat
  hread32 : ∀ (word : RiscV.Word 64),
    ((panSemBitVec64MemoryAccess execState).read32
        (panSemBitVec64MemoryAccess execState).domain memory bytesInWord word).map PanValue.word
      = (panMemLoad32HOL state.memory state.memaddrs state.be word).map
          (fun value => PanValue.word (BitVec.ofNat 64 value.toNat))
  hreadByte : ∀ (word : RiscV.Word 64),
    ((panSemBitVec64MemoryAccess execState).readByte
        (panSemBitVec64MemoryAccess execState).domain memory bytesInWord word).map PanValue.word
      = (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
          (fun byte => PanValue.word (BitVec.ofNat 64 byte.toNat))

 /-- Whole-expression production-to-`evalHOL` capstone assembled from every landed
    per-clause bridge by induction on the expression, under the bundled relation
    `PanValueEvalRel`.  The `wordOp`/compare/shift/read32/readByte codec fields are
    genuine hypotheses: the executed RV64 compare/shift codecs are not the HOL
    `word_cmp`/`word_sh` ones, so this is the honest complete-adapter statement.
    Untagged. -/
theorem evalPanValueExp_eq_evalHOL_of_rel {σ ffi : Type} [LawfulBEq String]
    (state : PanSemHolState 64 σ) [DecidablePred state.memaddrs]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress bytesInWord : RiscV.Word 64)
    (rel : PanValueEvalRel state execState structs locals globals memory baseAddress topAddress bytesInWord) :
    ∀ (expression : Exp (RiscV.Word 64)),
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          expression (memoryAccess := some (panSemBitVec64MemoryAccess execState))
        = (evalHOL state expression).map HolValue.toPanValue := by
  have hmain : ∀ (expression : Exp (RiscV.Word 64))
      (memoryAccess : Option (PanValueMemoryAccess (RiscV.Word 64))),
      (memoryAccess = some (panSemBitVec64MemoryAccess execState)) →
      evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          expression memoryAccess
        = (evalHOL state expression).map HolValue.toPanValue := by
    apply evalPanValueExp.induct
      (motive1 := fun expressions memoryAccess =>
        (memoryAccess = some (panSemBitVec64MemoryAccess execState)) →
        ∀ e ∈ expressions,
          evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
              e memoryAccess
            = (evalHOL state e).map HolValue.toPanValue)
      (motive2 := fun expression memoryAccess =>
        (memoryAccess = some (panSemBitVec64MemoryAccess execState)) →
        evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
            expression memoryAccess
          = (evalHOL state expression).map HolValue.toPanValue)
      (motive3 := fun fields memoryAccess =>
        (memoryAccess = some (panSemBitVec64MemoryAccess execState)) →
        ∀ p ∈ fields,
          evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
              p.2 memoryAccess
            = (evalHOL state p.2).map HolValue.toPanValue)
    · intro memoryAccess hm e he
      simp at he
    · intro expression expressions memoryAccess ihHead ihTail hm e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ihHead hm
      · exact ihTail hm e he
    · intro memoryAccess payload hm
      subst hm
      exact evalPanValueExp_const_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState)) payload
    · intro memoryAccess name hm
      subst hm
      exact evalPanValueExp_var_local_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        name rel.hlocals
    · intro memoryAccess name hm
      subst hm
      exact evalPanValueExp_var_global_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        name rel.hglobals
    · intro fields memoryAccess ih hm
      subst hm
      exact evalPanValueExp_rStruct_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        fields (fun e he => ih rfl e he)
    · intro index value memoryAccess ih hm
      subst hm
      exact evalPanValueExp_rField_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        index value (ih rfl)
    · intro name fields memoryAccess ih hm
      subst hm
      exact evalPanValueExp_nStruct_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        name fields rel.hstructs (fun e he => ih rfl e he)
    · intro name value memoryAccess ih hm
      subst hm
      exact evalPanValueExp_nField_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        name value rel.hstructs (ih rfl)
    · intro shape address memoryAccess ih hm
      subst hm
      exact evalPanValueExp_load_eq_evalHOL_anyShape state execState memory structs locals
        globals baseAddress topAddress bytesInWord shape address (ih rfl)
        rel.hstructs rel.hmem rel.hdom rel.hbytes
    · intro address memoryAccess ih hm
      subst hm
      exact evalPanValueExp_load32_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (panSemBitVec64MemoryAccess execState)
        address (ih rfl) rel.hread32
    · intro address memoryAccess ih hm
      subst hm
      exact evalPanValueExp_loadByte_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (panSemBitVec64MemoryAccess execState)
        address (ih rfl) rel.hreadByte
    · intro operator arguments memoryAccess ih hm
      subst hm
      exact evalPanValueExp_op_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (panSemBitVec64MemoryAccess execState)
        operator arguments (fun e he => ih rfl e he) rel.hwordOp
    · intro operator arguments memoryAccess ih hm
      subst hm
      exact evalPanValueExp_panOp_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState))
        operator arguments (fun e he => ih rfl e he)
    · intro operator left right memoryAccess ihLeft ihRight hm
      subst hm
      exact evalPanValueExp_cmp_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (panSemBitVec64MemoryAccess execState)
        operator left right (ihLeft rfl) (ihRight rfl) rel.hcmp
    · intro operator left right memoryAccess ihLeft ihRight hm
      subst hm
      exact evalPanValueExp_shift_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (panSemBitVec64MemoryAccess execState)
        operator left right (ihLeft rfl) (ihRight rfl) rel.hshift
    · intro memoryAccess hm
      subst hm
      exact evalPanValueExp_baseAddr_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState)) rel.hbase
    · intro memoryAccess hm
      subst hm
      exact evalPanValueExp_topAddr_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState)) rel.htop
    · intro memoryAccess hm
      subst hm
      exact evalPanValueExp_bytesInWord_eq_evalHOL state structs locals globals memory
        baseAddress topAddress bytesInWord (some (panSemBitVec64MemoryAccess execState)) rel.hbytes
    · intro memoryAccess hm p hp
      simp at hp
    · intro pair pairs tail access ihHead ihTail hm q hq
      rcases List.mem_cons.mp hq with hqhead | hqtail
      · subst hqhead
        exact ihHead hm
      · exact ihTail hm q hqtail
  intro expression
  exact hmain expression (some (panSemBitVec64MemoryAccess execState)) rfl

end

/-! ## Unconditional executed-path capstone (`flapjack-pxn.18.3.6.9.2.18.1`)

An **observational projection** of an executed `PanSemState` into the
`PanSemHolState` shape that `evalHOL` reads.  It is not an exact whole-state
port: `code`/`eshapes`/`shMemaddrs` are set to defaults (they do not affect
`evalHOL` expression evaluation) and `memaddrs` is narrowed to the
word-defined cells `panValueFlatMachineDomain execState memory`.  The
`memory`/`structs`/`locals`/`globals`/base/top arguments are supplied
independently; the wrapper `evalPanValueExp_eq_evalHOL_state` instantiates them
from `execState`.  Because the executed RV64 compare/shift codec equalities and
the byte/word load bridges are now proved, this projected state satisfies
`PanValueEvalRel` unconditionally, so `evalPanValueExp` agrees with `evalHOL` on
the executed path.  Untagged production-side adapter. -/
abbrev machineHolState (execState : PanSemState (RiscV.Word 64) ffi)
    (holFfi : FfiState ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress : RiscV.Word 64) : PanSemHolState 64 ffi where
  locals := fun name => (locals name).map PanValue.toHolValue
  globals := fun name => (globals name).map PanValue.toHolValue
  structs := structs.toHOL
  code := fun _ => none
  eshapes := fun _ => none
  memory := panValueWordHOL memory
  memaddrs := panValueFlatMachineDomain execState memory
  shMemaddrs := fun _ => False
  clock := execState.clock
  be := execState.be
  ffi := holFfi
  baseAddr := baseAddress
  topAddr := topAddress

instance machineHolStateDecidablePred (execState : PanSemState (RiscV.Word 64) ffi)
    (holFfi : FfiState ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress : RiscV.Word 64) :
    DecidablePred
      (machineHolState execState holFfi memory structs locals globals baseAddress topAddress).memaddrs :=
  fun a => inferInstanceAs
    (Decidable (execState.memaddrs a && panValueWordDefined memory a = true))

/-- The projected state above satisfies the bundled relation, unconditionally. -/
theorem panValueEvalRel_machineHolState
    (execState : PanSemState (RiscV.Word 64) ffi)
    (holFfi : FfiState ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress : RiscV.Word 64) :
    PanValueEvalRel
        (machineHolState execState holFfi memory structs locals globals baseAddress topAddress)
        execState structs locals globals memory baseAddress topAddress panSemBitVec64BytesInWord := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro name
    rw [Option.map_map]
    rw [show (HolValue.toPanValue ∘ PanValue.toHolValue)
        = (id : PanValue (RiscV.Word 64) → PanValue (RiscV.Word 64)) from
      by funext a; exact PanValue.toHolValue_toPanValue a]
    rw [Option.map_id]
    rfl
  · intro name
    rw [Option.map_map]
    rw [show (HolValue.toPanValue ∘ PanValue.toHolValue)
        = (id : PanValue (RiscV.Word 64) → PanValue (RiscV.Word 64)) from
      by funext a; exact PanValue.toHolValue_toPanValue a]
    rw [Option.map_id]
    rfl
  · exact fun op values => panSemBitVec64MemoryAccess_wordOp execState op values
  · intro op l r
    exact panRiscVCmp_eq_wordCmpResultHOL (width := 64) op l r
  · intro op l r
    exact panRiscVShift_eq_wordShiftHOL (width := 64) op l r
  · intro word
    have h := panSemBitVec64Read32_eq_panMemLoad32HOL execState memory word
    rw [h, Option.map_map]
    rfl
  · intro word
    have h := panSemBitVec64ReadByte_eq_panMemLoadByteHOL execState memory word
    rw [h, Option.map_map]
    rfl

/-- Unconditional executed-path capstone: on the projected state built from the
executed `PanSemState`, `evalPanValueExp` agrees with the exact tagged `evalHOL`.
The `memory`/`structs`/`locals`/`globals`/base/top arguments may be supplied
independently; `evalPanValueExp_eq_evalHOL_state` instantiates them from
`execState`.  Untagged. -/
theorem evalPanValueExp_eq_evalHOL_executed {ffi : Type} [LawfulBEq String]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (holFfi : FfiState ffi)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (RiscV.Word 64)))
    (baseAddress topAddress : RiscV.Word 64)
    (expression : Exp (RiscV.Word 64)) :
    evalPanValueExp structs locals globals memory baseAddress topAddress panSemBitVec64BytesInWord
        expression (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL
            (machineHolState execState holFfi memory structs locals globals baseAddress topAddress)
            expression).map HolValue.toPanValue :=
  evalPanValueExp_eq_evalHOL_of_rel _ execState structs locals globals memory baseAddress topAddress
    panSemBitVec64BytesInWord
    (panValueEvalRel_machineHolState execState holFfi memory structs locals globals baseAddress
      topAddress)
    expression

/-- Actual-state corollary: `evalPanValueExp` run over the executed
`PanSemState`'s own `structs`/`locals`/`globals`/`memory`/base/top agrees with
the tagged `evalHOL` over the observational projection `machineHolState`.
Untagged. -/
theorem evalPanValueExp_eq_evalHOL_state {ffi : Type} [LawfulBEq String]
    (execState : PanSemState (RiscV.Word 64) ffi)
    (holFfi : FfiState ffi)
    (expression : Exp (RiscV.Word 64)) :
    evalPanValueExp execState.structs execState.locals execState.globals execState.memory
        execState.baseAddress execState.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess execState))
      = (evalHOL
            (machineHolState execState holFfi execState.memory execState.structs
              execState.locals execState.globals execState.baseAddress execState.topAddress)
            expression).map HolValue.toPanValue :=
  evalPanValueExp_eq_evalHOL_executed execState holFfi execState.memory execState.structs
    execState.locals execState.globals execState.baseAddress execState.topAddress expression

/-! ## Exact HOL `panSem` state-access helper definitions (flapjack-pxn.18.4.3.77.8)

These are the small definitions in `cakeml/pancake/semantics/panSemScript.sml`
that the total statement clauses (notably `ShMemLoad`/`ShMemStore` and
`is_valid_value`) are phrased over. -/

/-- Exact HOL `nb_op` (`panSemScript.sml:549`): the byte width sent as the
shared-memory size byte for each `OpSize` (`OpW` is the full word, width 0). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "nb_op_def"]
def nbOpHOL : OpSize → Nat
  | .op8 => 1
  | .op16 => 2
  | .opW => 0
  | .op32 => 4

/-- FLAPJACK-SPECIFIC (not an exact HOL port). Source-shaped counterpart of HOL
`lookup_kvar` (`panSemScript.sml:415`), but the key type does not match: HOL
`varname` is `mlstring` whereas the Lean state uses `VarName = String`. The
`@[hol]` tag is therefore withheld; an exact port keyed by `MlString` is tracked
by the dependency bead `flapjack-pxn.18.4.3.77.8.1`. -/
def lookupKvarHOL {width : Nat} (kind : VarKind) (name : VarName)
    (state : PanSemHolState width σ) : Option (HolValue width) :=
  match kind with
  | .local => state.locals name
  | .global => state.globals name

/-- FLAPJACK-SPECIFIC (not an exact HOL port). Source-shaped counterpart of HOL
`set_kvar` (`panSemScript.sml:403`), but the key type does not match (HOL
`varname` is `mlstring`, Lean `VarName` is `String`). The `@[hol]` tag is
therefore withheld; an exact port keyed by `MlString` is tracked by the
dependency bead `flapjack-pxn.18.4.3.77.8.1`. -/
def setKvarHOL {width : Nat} (kind : VarKind) (name : VarName)
    (value : HolValue width) (state : PanSemHolState width σ) : PanSemHolState width σ :=
  match kind with
  | .local =>
      { state with
        locals := fun current => if current = name then some value else state.locals current }
  | .global =>
      { state with
        globals := fun current => if current = name then some value else state.globals current }

end Flapjack
