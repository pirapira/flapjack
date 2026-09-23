import Flapjack.PanBst
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

private def panSemBitVec64WordModel : PanMemoryModel (RiscV.Word 64) := by
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

end Flapjack
