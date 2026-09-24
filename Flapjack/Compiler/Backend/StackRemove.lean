import Flapjack.Compiler.Backend.StackCarrier
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Pancake.WordLang
import Flapjack.HolRef

/-!
# Stack-remove / stack-alloc `make_init` prerequisites

The `make_init` / `init_reduce` / `init_prop` chain of
`cakeml/compiler/backend/proofs/stack_removeProofScript.sml` and
`.../stack_allocProofScript.sml` reads the machine memory through the helpers
below.  This module ports the small, state-free prerequisites exactly, width
indexed over `'a word` as in HOL:

* `wordLangScript.sml:331-333` `word_loc = Word ('a word) | Loc num num`
  (ported in `Flapjack.Pancake.WordLang`);
* `stack_removeProofScript.sml:144-146` `is_SOME_Word`;
* `stack_removeProofScript.sml:2739-2742` `read_mem` and its `LENGTH_read_mem`;
* `stack_removeProofScript.sml:2745-2748` `addresses` and its `IN_addresses`;
* `stack_removeScript.sml:16-56` `max_stack_alloc`, `word_offset`,
  `store_list`, `store_length`, and `stack_err_lab`.

`bytes_in_word` is HOL's fixed `n2w (dimindex (:'a) DIV 8)`; here
`bytesInWord width = BitVec.ofNat width (width / 8)`.

The theorem-shaped declarations carry `@[hol ...]` tags (statements match the
HOL sources); no state record or evaluator is asserted.
-/

namespace Flapjack.Compiler.Backend.StackRemove

open Flapjack
open Flapjack.Compiler.Backend.StackLang

/-- HOL `bytes_in_word` at width `width` (`n2w (dimindex (:'a) DIV 8)`). -/
def bytesInWord (width : Nat) : BitVec width := BitVec.ofNat width (width / 8)

/-- HOL `is_SOME_Word` (`cakeml/compiler/backend/proofs/stack_removeProofScript.sml:144-146`),
width-indexed: HOL's `word_loc` payload is the actual `'a word`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "is_SOME_Word_def"]
def isSomeWord {width : Nat} [NeZero width] : Option (WordLoc (BitVec width)) → Bool
  | some (.word _) => true
  | _ => false

/-- HOL `read_mem` (`cakeml/compiler/backend/proofs/stack_removeProofScript.sml:2739-2742`). -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "read_mem_def"]
def readMem {width : Nat} (address : BitVec width)
    (memory : BitVec width → WordLoc (BitVec width)) : Nat → List (WordLoc (BitVec width))
  | 0 => []
  | n + 1 => memory address :: readMem (address + bytesInWord width) memory n

/-- HOL `addresses` (`cakeml/compiler/backend/proofs/stack_removeProofScript.sml:2745-2748`).
HOL sets are predicates, so the Lean carrier is `BitVec width → Prop`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "addresses_def"]
def addresses {width : Nat} (address : BitVec width) : Nat → (BitVec width → Prop)
  | 0 => fun _ => False
  | n + 1 => fun x => x = address ∨ addresses (address + bytesInWord width) n x

/-- HOL `LENGTH_read_mem`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "LENGTH_read_mem"]
theorem length_readMem {width : Nat} (n : Nat) (address : BitVec width)
    (memory : BitVec width → WordLoc (BitVec width)) :
    (readMem address memory n).length = n := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih => simp only [readMem, List.length_cons, ih]

/-- HOL `IN_addresses`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "IN_addresses"]
theorem mem_addresses {width : Nat} (n : Nat) (address x : BitVec width) :
    addresses address n x ↔
      ∃ i, i < n ∧ x = address + BitVec.ofNat width i * bytesInWord width := by
  induction n generalizing address with
  | zero =>
      simp only [addresses, false_iff, not_exists]
      intro i hi
      omega
  | succ n ih =>
      simp only [addresses, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by omega, by simp⟩
        · refine ⟨i + 1, by omega, ?_⟩
          rw [BitVec.ofNat_add]
          simp only [BitVec.one_mul, BitVec.add_mul]
          ac_rfl
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl (by simp)
        | succ i =>
            refine Or.inr ⟨i, by omega, ?_⟩
            rw [BitVec.ofNat_add]
            simp only [BitVec.one_mul, BitVec.add_mul]
            ac_rfl

/-! ## Value helpers from the `stack_remove` compiler script

`cakeml/compiler/backend/stack_removeScript.sml` drives the stack operations
through these state-free value helpers.  They are ported exactly and width
indexed over `'a word` as in HOL.  `store_pos`/`store_offset` are deferred
(they depend on HOL core `INDEX_FIND` and on decidable `store_name` equality,
which is tracked separately). -/

/-- HOL `max_stack_alloc` (`stack_removeScript.sml:16-18`). -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "max_stack_alloc_def"]
def maxStackAlloc : Nat := 255

/-- HOL `word_offset` (`stack_removeScript.sml:20-22`):
`word_offset n = n2w (dimindex (:'a) DIV 8 * n)`. HOL word dimensions are
nonzero (`dimindex (:'a) > 0`), so the exact carrier requires `[NeZero width]`. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "word_offset_def"]
def wordOffset {width : Nat} [NeZero width] (n : Nat) : BitVec width :=
  BitVec.ofNat width ((width / 8) * n)

/-- HOL `store_list` (`stack_removeScript.sml:24-35`): the sixteen fixed store
names followed by `Temp 00w .. Temp 31w`. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "store_list_def"]
def storeList : List StoreName :=
  [.nextFree, .endOfHeap, .heapLength, .otherHeap, .triggerGC, .allocSize,
   .handler, .globals, .globReal, .progStart, .bitmapBase, .genStart,
   .codeBuffer, .codeBufferEnd, .bitmapBuffer, .bitmapBufferEnd,
   .temp (BitVec.ofNat 5 0), .temp (BitVec.ofNat 5 1),
   .temp (BitVec.ofNat 5 2), .temp (BitVec.ofNat 5 3),
   .temp (BitVec.ofNat 5 4), .temp (BitVec.ofNat 5 5),
   .temp (BitVec.ofNat 5 6), .temp (BitVec.ofNat 5 7),
   .temp (BitVec.ofNat 5 8), .temp (BitVec.ofNat 5 9),
   .temp (BitVec.ofNat 5 10), .temp (BitVec.ofNat 5 11),
   .temp (BitVec.ofNat 5 12), .temp (BitVec.ofNat 5 13),
   .temp (BitVec.ofNat 5 14), .temp (BitVec.ofNat 5 15),
   .temp (BitVec.ofNat 5 16), .temp (BitVec.ofNat 5 17),
   .temp (BitVec.ofNat 5 18), .temp (BitVec.ofNat 5 19),
   .temp (BitVec.ofNat 5 20), .temp (BitVec.ofNat 5 21),
   .temp (BitVec.ofNat 5 22), .temp (BitVec.ofNat 5 23),
   .temp (BitVec.ofNat 5 24), .temp (BitVec.ofNat 5 25),
   .temp (BitVec.ofNat 5 26), .temp (BitVec.ofNat 5 27),
   .temp (BitVec.ofNat 5 28), .temp (BitVec.ofNat 5 29),
   .temp (BitVec.ofNat 5 30), .temp (BitVec.ofNat 5 31)]

/-- HOL `store_length` (`stack_removeScript.sml:37-42`): the even-rounded
length of `store_list`. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "store_length_def"]
def storeLength : Nat :=
  if storeList.length % 2 = 0 then storeList.length else storeList.length + 1

/-- HOL `stack_err_lab` (`stack_removeScript.sml:54-56`). -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stack_err_lab_def"]
def stackErrLab : Nat := 2

/-!
## Instruction overloads and `halt_inst`

HOL `stackLangScript.sml:80-84` declares the `left_shift_inst`,
`right_shift_inst`, `const_inst`, `load_inst`, and `store_inst` overloads, and
`stack_removeScript.sml:58-60` defines `halt_inst` on top of `const_inst` and
`Halt`.  The Lean implementations below are stated over
`StackCarrier.ProgW (BitVec width)`.

These declarations are deliberately UNTAGGED. HOL's `stackLang$prog` has a
fixed `mlstring` FFI field; our `ProgW` carrier uses Lean `String` for that
field, so `ProgW (BitVec width)` is not yet an exact HOL carrier
and a `@[hol]` tag on a definition using it would over-claim.  The overload
bodies match HOL's constructors, and they are exercised by the direct HOL
oracle and the untagged parity test.  The exact `mlstring`/program carrier and
the bridges that would let these be re-tagged are tracked by bead
`flapjack-pxn.18.5.15.3.11.2`.
-/

/-- HOL `left_shift_inst` (`cakeml/compiler/backend/stackLangScript.sml:80`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def leftShiftInst {width : Nat} (register value : Nat) :
    StackCarrier.ProgW (BitVec width) :=
  .inst (.arith (.shift .lsl register register (.imm (BitVec.ofNat width value))))

/-- HOL `right_shift_inst` (`cakeml/compiler/backend/stackLangScript.sml:81`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def rightShiftInst {width : Nat} (register value : Nat) :
    StackCarrier.ProgW (BitVec width) :=
  .inst (.arith (.shift .lsr register register (.imm (BitVec.ofNat width value))))

/-- HOL `const_inst` (`cakeml/compiler/backend/stackLangScript.sml:82`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def constInst {width : Nat} (register : Nat) (value : BitVec width) :
    StackCarrier.ProgW (BitVec width) :=
  .inst (.const register value)

/-- HOL `load_inst` (`cakeml/compiler/backend/stackLangScript.sml:83`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def loadInst {width : Nat} (register address : Nat) :
    StackCarrier.ProgW (BitVec width) :=
  .inst (.mem .load register (.addr address 0))

/-- HOL `store_inst` (`cakeml/compiler/backend/stackLangScript.sml:84`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def storeInst {width : Nat} (register address : Nat) :
    StackCarrier.ProgW (BitVec width) :=
  .inst (.mem .store register (.addr address 0))

/-- HOL `halt_inst` (`cakeml/compiler/backend/stack_removeScript.sml:58-60`),
untagged pending the exact `mlstring` carrier (bead .18.5.15.3.11.2). -/
def haltInst {width : Nat} (value : BitVec width) :
    StackCarrier.ProgW (BitVec width) :=
  .seq (.inst (.const 1 value)) (.halt 1)

end Flapjack.Compiler.Backend.StackRemove
