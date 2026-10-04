import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit
import Flapjack.Misc.Alignment
import Flapjack.Misc.WordList

/-! `init_store_ok_def` (`data_to_word_gcProofScript.sml:4569-4598`): the store,
memory and buffers of the initial word state, as established by the stack
initialization. HOL's `FLOOKUP store n` is `store.lookup n`, `bytes_in_word` is
`wordSemBytesInWord`, `n2w` is `BitVec.ofNat width`, and the memory domain
`dm : 'a word set` is a Boolean predicate whose graph `fun2set (m,dm)` is
`fun2Set (m, fun a => dm a = true)`, as in the reviewed `init_prop`. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Pancake

/-- HOL `init_store_ok_def`. HOL's memory values `'b`, and the code and data
buffers' element widths `'c` and `'d`, are unconstrained; they stay generic. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "init_store_ok_def"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
def initStoreOk {width : Nat} [NeZero width] {β : Type} {cw dw : Nat} [NeZero cw] [NeZero dw]
    (c : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → β) (dm : BitVec width → Bool) (codeBuffer : WordSemBuffer width cw)
    (dataBuffer : WordSemBuffer width dw) : Prop :=
  ∃ (limit : Nat) (curr : BitVec width),
    limit ≤ maxHeapLimit width c ∧
    store.lookup .globals = some (.word 0) ∧
    store.lookup .globReal = some (.word curr) ∧
    store.lookup .genStart = some (.word 0) ∧
    store.lookup .currHeap = some (.word curr) ∧
    store.lookup .otherHeap = store.lookup .endOfHeap ∧
    store.lookup .nextFree = some (.word curr) ∧
    store.lookup .endOfHeap =
      some (.word (curr + wordSemBytesInWord * BitVec.ofNat width limit)) ∧
    store.lookup .triggerGC =
      some (.word (match c.gcKind with
        | .generational _ => curr
        | _ => curr + wordSemBytesInWord * BitVec.ofNat width limit)) ∧
    store.lookup .heapLength = some (.word (wordSemBytesInWord * BitVec.ofNat width limit)) ∧
    store.lookup .codeBuffer = some (.word codeBuffer.position) ∧
    store.lookup .codeBufferEnd =
      some (.word (codeBuffer.position + BitVec.ofNat width codeBuffer.spaceLeft)) ∧
    store.lookup .bitmapBuffer = some (.word dataBuffer.position) ∧
    store.lookup .bitmapBufferEnd =
      some (.word (dataBuffer.position +
        wordSemBytesInWord * BitVec.ofNat width dataBuffer.spaceLeft)) ∧
    codeBuffer.buffer = [] ∧
    dataBuffer.buffer = [] ∧
    Misc.wordListExists curr (limit + limit) (SetSep.fun2Set (m, fun a => dm a = true)) ∧
    holByteAligned curr = true

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
