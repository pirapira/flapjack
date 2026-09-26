import Flapjack.HolRef
import Flapjack.Misc.GoodDimindex
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip
import Flapjack.Pancake.Semantics.LoopSem

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

/-- Exact statement of HOL `panProps$read_write_bytearray_lemma`
    (`cakeml/pancake/semantics/panPropsScript.sml:1119`). Reading `length`
    bytes with the aligned, in-domain byte loader `panMemLoadByteHOL` and then
    writing the same bytes back with `panWriteBytearrayHOL` leaves the memory
    unchanged, provided the word width is `good_dimindex` (32 or 64).

    The carriers are the exact panSem ones: the total `word_lab` memory is
    `RiscV.Word width → HolWordLab width`, the HOL address set is a `Prop`
    predicate with `DecidablePred` evidence, `word8` is `UInt8`, the reader is
    the tagged `panMemLoadByteHOL` (`mem_load_byte_def`) fed to the tagged
    `readBytearrayHOL` (`read_bytearray_def`), and the write is the tagged
    `panWriteBytearrayHOL` (`write_bytearray_def`). HOL's `good_dimindex` is
    `goodDimindex` (`Flapjack/Misc/GoodDimindex.lean`). The proof inducts on the
    length like HOL, splitting `goodDimindex` to `width = 32 ∨ width = 64` and
    using the width-generic byte roundtrip `panSetByteHOL_panGetByteHOL`
    (`PanSem/ByteRoundtrip.lean`, the untagged analogue of standard-library
    `byte$set_byte_get_byte`) where HOL uses `set_byte_get_byte`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "read_write_bytearray_lemma"]
theorem readWriteBytearrayLemma {width : Nat} [NeZero width]
    (length : Nat) (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) :
    (goodDimindex width ∧
      readBytearrayHOL address length
        (panMemLoadByteHOL memory domain bigEndian) = some bytes) →
      panWriteBytearrayHOL address bytes memory domain bigEndian = memory := by
  rintro ⟨hgood, hread⟩
  have hwidth : 8 ≤ width := by
    rcases (by simpa only [goodDimindex] using hgood) with h | h <;> omega
  induction length generalizing address bytes with
  | zero =>
      simp only [readBytearrayHOL] at hread
      have hbytes : bytes = [] := by simpa using hread.symm
      subst bytes
      rfl
  | succ n ih =>
      rw [readBytearrayHOL] at hread
      cases hload : panMemLoadByteHOL memory domain bigEndian address with
      | none =>
          simp only [hload] at hread
          exact absurd hread (Option.some_ne_none bytes).symm
      | some b =>
          simp only [hload] at hread
          cases hrest : readBytearrayHOL (address + 1) n
              (panMemLoadByteHOL memory domain bigEndian) with
          | none =>
              simp only [hrest] at hread
              exact absurd hread (Option.some_ne_none bytes).symm
          | some bs =>
              simp only [hrest] at hread
              have hbytes : bytes = b :: bs := by
                injection hread with h
                exact h.symm
              subst bytes
              have htail : panWriteBytearrayHOL (address + 1) bs memory domain
                  bigEndian = memory := ih (address + 1) bs hrest
              rw [panWriteBytearrayHOL, htail]
              cases hcell : memory (panByteAlignHOL (width := width) address) with
              | word v =>
                  by_cases hdom :
                      domain (panByteAlignHOL (width := width) address)
                  · have hb : b = panGetByteHOL address v bigEndian := by
                      have hEq : some (panGetByteHOL address v bigEndian) = some b := by
                        simpa only [panMemLoadByteHOL, hcell, hdom, if_true] using hload
                      injection hEq with h
                      exact h.symm
                    have hstore : panMemStoreByteHOL memory domain bigEndian address b
                        = some (fun current =>
                            if current = panByteAlignHOL (width := width) address then
                              .word (panSetByteHOL address
                                (BitVec.ofNat width b.toNat) v bigEndian)
                            else memory current) := by
                      simp only [panMemStoreByteHOL, hcell, hdom, if_true]
                    rw [hstore]
                    dsimp only
                    funext current
                    by_cases hcur :
                        current = panByteAlignHOL (width := width) address
                    · subst hcur
                      rw [if_pos rfl, hcell]
                      congr 1
                      rw [hb]
                      exact panSetByteHOL_panGetByteHOL address v bigEndian hwidth
                    · rw [if_neg hcur]
                  · exfalso
                    simp only [panMemLoadByteHOL, hcell, hdom, if_false] at hload
                    exact absurd hload (Option.some_ne_none b).symm

end Flapjack
