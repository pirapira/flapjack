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
  let aligned := RiscV.panRiscVByteAlign (BitVec.ofNat width (width / 8)) address
  match memory aligned with
  | .word value =>
      if domain aligned then
        some (UInt8.ofNat
          (RiscV.panRiscVGetByteEndian (BitVec.ofNat width (width / 8)) address
            value bigEndian).toNat)
      else none

end Flapjack
