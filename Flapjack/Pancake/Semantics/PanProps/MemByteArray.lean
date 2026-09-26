import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# PanProps byte-array memory invariants

The source review for `write_bytearray_update_byte`
(`cakeml/pancake/semantics/panPropsScript.sml:1098`) checked the theorem against
`panSemScript.sml:300-316` and the exact standard-library alignment operations.
HOL quantifies over a byte list (`word8 list`), two addresses, a total
`word_lab` memory, an address set, and endianness. It assumes `byte_aligned ad`
and `m ad = Word w`, then concludes that the recursive bytearray write still
returns a word at `ad`. Here `byte_aligned ad` is represented by the fixed-point
equation `panByteAlignHOL ad = ad`; `UInt8` is the fixed 8-bit byte carrier,
`HolWordLab` is the exact `word_lab` carrier, and the domain is a `Prop` set
with Lean decidability evidence. All HOL premises and the existential result
are preserved. The proof establishes the stronger preservation statement
without needing the alignment premise.
-/

namespace Flapjack

private theorem panMemStoreByteHOL_preservesWordAt {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (storeAddress target : RiscV.Word width) (byte : UInt8)
    (oldWord : RiscV.Word width) (hMemory : memory target = .word oldWord) :
    match panMemStoreByteHOL memory domain bigEndian storeAddress byte with
    | some updated => ∃ newWord, updated target = .word newWord
    | none => True := by
  cases hCell : memory (panByteAlignHOL (width := width) storeAddress) with
  | word cell =>
      by_cases hDomain : domain (panByteAlignHOL (width := width) storeAddress)
      · by_cases hTarget : target = panByteAlignHOL (width := width) storeAddress
        · subst target
          simp [panMemStoreByteHOL, hCell, hDomain]
        · simp [panMemStoreByteHOL, hCell, hDomain, hTarget, hMemory]
      · simp [panMemStoreByteHOL, hDomain]

private theorem panWriteBytearrayHOL_preservesWordAt {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (target oldWord : RiscV.Word width)
    (hMemory : memory target = .word oldWord) :
    ∃ newWord,
      panWriteBytearrayHOL address bytes memory domain bigEndian target = .word newWord := by
  induction bytes generalizing address memory with
  | nil =>
      exact ⟨oldWord, by simpa [panWriteBytearrayHOL] using hMemory⟩
  | cons byte rest ih =>
      have hTail : ∃ tailWord,
          panWriteBytearrayHOL (address + 1) rest memory domain bigEndian target =
            .word tailWord :=
        ih (address + 1) memory hMemory
      rcases hTail with ⟨tailWord, hTail⟩
      simp only [panWriteBytearrayHOL]
      cases hStore : panMemStoreByteHOL
          (panWriteBytearrayHOL (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | none =>
          exact ⟨oldWord, by simpa [hStore] using hMemory⟩
      | some updated =>
          have hUpdated := panMemStoreByteHOL_preservesWordAt
            (panWriteBytearrayHOL (address + 1) rest memory domain bigEndian)
            domain bigEndian address target byte tailWord hTail
          simp only [hStore] at hUpdated
          rcases hUpdated with ⟨newWord, hNewWord⟩
          exact ⟨newWord, by simpa [hStore] using hNewWord⟩

/-- Flapjack-specific word-tag preservation helper related to HOL
    `panProps$write_bytearray_update_byte` (`panPropsScript.sml:1098`). This
    stronger helper assumes a selected `word` witness and proves preservation
    after any bytearray write. It is deliberately untagged: HOL's exact premise
    is one implication antecedent containing
    `byte_aligned ad ∧ (∃w, memory ad = Word w)`, while this helper currently
    presents the witness and alignment as separate binders. The faithful exact
    statement is tracked by `flapjack-4ac.4.58.1`. -/
theorem panWriteBytearrayPreservesWordAt {width : Nat} [NeZero width]
    (bytes : List UInt8) (address address' : RiscV.Word width)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (_aligned : panByteAlignHOL (width := width) address = address)
    (word : RiscV.Word width)
    (hMemory : memory address = .word word) :
    ∃ updatedWord,
      panWriteBytearrayHOL address' bytes memory domain bigEndian address =
        .word updatedWord := by
  exact panWriteBytearrayHOL_preservesWordAt address' bytes memory domain bigEndian
    address word hMemory

/-- Exact statement of HOL `write_bytearray_update_byte`. HOL's
`byte_aligned ad` is `byte_align ad = ad` (`alignmentScript.sml:27`), rendered
here with `panByteAlignHOL`; HOL `word8 list` is `List UInt8`. The HOL word
width remains polymorphic, as does this theorem's `width`. Unlike the support
lemma above, the alignment and existential word premise form one antecedent. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "write_bytearray_update_byte"]
theorem writeBytearrayUpdateByte {width : Nat} [NeZero width]
    (bytes : List UInt8) (address address' : RiscV.Word width)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) :
    (panByteAlignHOL address = address ∧
      (∃ word : RiscV.Word width, memory address = .word word)) →
      ∃ word : RiscV.Word width,
        panWriteBytearrayHOL address' bytes memory domain bigEndian address = .word word := by
  rintro ⟨haligned, word, hmemory⟩
  exact panWriteBytearrayPreservesWordAt bytes address address' memory domain
    bigEndian haligned word hmemory

end Flapjack
