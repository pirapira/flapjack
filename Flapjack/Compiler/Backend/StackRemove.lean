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
* `stack_removeProofScript.sml:2745-2748` `addresses` and its `IN_addresses`.

`bytes_in_word` is HOL's fixed `n2w (dimindex (:'a) DIV 8)`; here
`bytesInWord width = BitVec.ofNat width (width / 8)`.

The theorem-shaped declarations carry `@[hol ...]` tags (statements match the
HOL sources); no state record or evaluator is asserted.
-/

namespace Flapjack.Compiler.Backend.StackRemove

open Flapjack

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

end Flapjack.Compiler.Backend.StackRemove