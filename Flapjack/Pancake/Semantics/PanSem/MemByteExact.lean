import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip
import Flapjack.Pancake.Semantics.LoopSem

/-!
# Exact `read_write_bytearray_lemma` over the panSem HOL carriers

This module ports HOL `panProps$read_write_bytearray_lemma`
(`cakeml/pancake/semantics/panPropsScript.sml:1119`):

```
read_write_bytearray_lemma:
  ∀n addr bytes.
    good_dimindex(:α) ∧
    read_bytearray (addr:α word) n (mem_load_byte m addrs be) = SOME bytes
    ⇒ write_bytearray addr bytes m addrs be = m
```

The statement uses the exact carriers already present in this tree: the total
`word_lab` memory is `RiscV.Word width → HolWordLab width`, the HOL address set
`addrs` is a `Prop` predicate with `DecidablePred` evidence, `word8` is `UInt8`,
the byte reader is the tagged `panMemLoadByteHOL` (`mem_load_byte_def`), the
reader combinator is the tagged `readBytearrayHOL` (`read_bytearray_def`), and
the write is the tagged `panWriteBytearrayHOL` (`write_bytearray_def`). HOL's
`good_dimindex` (`cakeml/misc/miscScript.sml:4315`) is ported as `goodDimindex`.

The proof follows HOL: induction on the length, using the width-generic byte
roundtrip `panSetByteHOL_panGetByteHOL` (`PanSem/ByteRoundtrip.lean`, the
untagged analogue of standard-library `byte$set_byte_get_byte`) after the
`good_dimindex` case split to `width = 32 ∨ width = 64`.
-/

namespace Flapjack

/-- Exact port of HOL `good_dimindex` (`cakeml/misc/miscScript.sml:4315`):
    `good_dimindex (:'a) ⇔ dimindex (:'a) = 32 ∨ dimindex (:'a) = 64`. The Lean
    word width is the HOL `dimindex`, so this is the same predicate. -/
@[hol "cakeml/misc/miscScript.sml" "good_dimindex_def"]
def goodDimindex (width : Nat) : Prop := width = 32 ∨ width = 64

/-- Exact statement of HOL `panProps$read_write_bytearray_lemma`
    (`cakeml/pancake/semantics/panPropsScript.sml:1119`). Reading `length`
    bytes with the aligned, in-domain byte loader `panMemLoadByteHOL` and then
    writing the same bytes back with `panWriteBytearrayHOL` leaves the memory
    unchanged, provided the word width is `good_dimindex` (32 or 64). -/
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
