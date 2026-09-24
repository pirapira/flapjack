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

/-! Statement-exact port of HOL `panSem$mem_load` (`cakeml/pancake/semantics/panSemScript.sml:137`,
    defining `mem_load`, `mem_loads`, and `mem_load_flds`).  The struct context is
    the HOL-shaped `StructContextHOL`; the memory is rendered as a total
    `HolWordLab` map with a `Prop` domain (HOL `'a word set`), and the recursive
    address advance is `addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)`
    with `bytesInWord = n2w (width / 8)`.  HOL's `Named` lookup
    `dropWhile (\(n,i). ~(n = nm)) stcs` is inlined as the equivalent structural
    scan over the context (needed for the Lean termination measure
    `(structs.length, sizeOf shape)`, the image of HOL's lexicographic
    `(LENGTH stcs, shape_size)`); the scan returns the first name match together
    with the remaining context, exactly the `(nm,info)::stcs'` HOL destructures. -/
mutual
  @[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_def"]
  def panMemLoadHOL {width : Nat} (structs : StructContextHOL) (bytesInWord : RiscV.Word width)
      (memory : RiscV.Word width → HolWordLab width) (domain : RiscV.Word width → Prop)
      [DecidablePred domain] (address : RiscV.Word width) : Shape → Option (HolValue width)
    | .one => if domain address then some (.val (memory address)) else none
    | .comb shapes =>
        match panMemLoadsHOL structs bytesInWord memory domain address shapes with
        | some values => some (.rStruct values)
        | none => none
    | .named name =>
        match structs with
        | [] => none
        | (candidate, info) :: rest =>
            if candidate == name then
              match panMemLoadFldsHOL rest bytesInWord memory domain address info.fields with
              | some fields => some (.nStruct candidate fields)
              | none => none
            else panMemLoadHOL rest bytesInWord memory domain address (.named name)
  termination_by _shape => (structs.length, sizeOf _shape)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  def panMemLoadsHOL {width : Nat} (structs : StructContextHOL) (bytesInWord : RiscV.Word width)
      (memory : RiscV.Word width → HolWordLab width) (domain : RiscV.Word width → Prop)
      [DecidablePred domain] (address : RiscV.Word width) : List Shape → Option (List (HolValue width))
    | [] => some []
    | shape :: shapes =>
        match panMemLoadHOL structs bytesInWord memory domain address shape,
              panMemLoadsHOL structs bytesInWord memory domain
                (address + bytesInWord * BitVec.ofNat width (sizeOfShWithCtxt structs shape)) shapes with
        | some value, some values => some (value :: values)
        | _, _ => none
  termination_by _shapes => (structs.length, sizeOf _shapes)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  def panMemLoadFldsHOL {width : Nat} (structs : StructContextHOL) (bytesInWord : RiscV.Word width)
      (memory : RiscV.Word width → HolWordLab width) (domain : RiscV.Word width → Prop)
      [DecidablePred domain] (address : RiscV.Word width) :
      List (FieldName × Shape) → Option (List (FieldName × HolValue width))
    | [] => some []
    | (field, shape) :: fields =>
        match panMemLoadHOL structs bytesInWord memory domain address shape,
              panMemLoadFldsHOL structs bytesInWord memory domain
                (address + bytesInWord * BitVec.ofNat width (sizeOfShWithCtxt structs shape)) fields with
        | some value, some values => some ((field, value) :: values)
        | _, _ => none
  termination_by _fields => (structs.length, sizeOf _fields)
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

end Flapjack
