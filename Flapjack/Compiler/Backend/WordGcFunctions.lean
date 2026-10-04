import Flapjack.HolRef
import Flapjack.Misc.Alignment
import Flapjack.Misc.ListEl
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.FiniteMapApply
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.GcShared
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# `word_gcFunctions`: shallow embedding of the word-level garbage collectors

The definitions of `cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml`
(lines 14-503): the copying collector (`word_full_gc`), the generational
collector (`word_gen_gc`) and its partial collection (`word_gen_gc_partial`),
and the store-level collector `word_gc_fun` that `stack_alloc` and `wordSem`
use as their `gc_fun_type`.

Carriers: HOL `'a word` is the positive-width `BitVec width`, `'a word_loc` is
`WordLocW width`, memory `'a word -> 'a word_loc` is a Lean function, the
memory domain `'a word set` is a `BitVec width → Bool` membership function (as in
`WordSemGcFun`), and the store `store_name |-> 'a word_loc` is the canonical
`HolFiniteMapExact WordStoreHOL (WordLocW width)`.  HOL's tupled arguments and
results stay tupled, in HOL order.  HOL `bytes_in_word` is
`wordSemBytesInWord`, `shift (:'a)` is `wordShiftAmount width`, `dimword (:'a)`
is `2 ^ width`, `theWord` is `wordSemTheWord`, `isWord` is `wordSemIsWordLoc`,
`is_fwd_ptr` is `wordSemIsFwdPtr`, `f ' x` is `holFapply`, `|++` is
`HolFiniteMapExact.updateListEq`, `HD` is `holHd` and `TL` is `List.tail`
(HOL `TL [] = []`).  The collector's `refs_to_addresses` is ported below over
the faithful `heap_element`/`heap_address` carriers in `GcShared`.
-/

namespace Flapjack.Compiler.Backend.WordGcFunctions

open Flapjack Flapjack.Compiler.Backend.DataToWord

instance wordLocWNonemptyGc {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word 0⟩

/-- HOL combinator `UPDATE` (`(a =+ b) f = λx. if a = x then b else f x`) on a
memory function.  Flapjack infrastructure (HOL source outside `cakeml/`). -/
def gcUpdate {width : Nat} [NeZero width] (a : BitVec width) (b : WordLocW width)
    (f : BitVec width → WordLocW width) : BitVec width → WordLocW width :=
  fun x => if a = x then b else f x

/-- HOL `word_bits h 0 w` (`(h -- 0) w`): the bits `0 .. MIN h (dimindex - 1)`
of `w`.  Flapjack infrastructure (HOL source outside `cakeml/`). -/
def gcWordBitsLow {width : Nat} (h : Nat) (w : BitVec width) : BitVec width :=
  BitVec.ofNat width (w.toNat % 2 ^ (h + 1))

theorem bitVec_toNat_sub_one_lt {width : Nat} {w : BitVec width} (h : w ≠ 0) :
    (w - 1).toNat < w.toNat := by
  have hw : w.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hlt := w.isLt
  have hpos : 0 < width := by
    rcases Nat.eq_zero_or_pos width with rfl | hp
    · simp at hlt; omega
    · exact hp
  have h1 : (1 : BitVec width).toNat = 1 := by
    simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow hpos]
  rw [BitVec.toNat_sub, h1]
  have : 2 ^ width - 1 + w.toNat = (w.toNat - 1) + 2 ^ width := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Exact HOL `bytes_in_word_mul_eq_shift` (`word_gcFunctionsScript.sml:15-21`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "bytes_in_word_mul_eq_shift"
  (words_as_type_indexed_bitvec)]
theorem bytesInWord_mul_eq_shift {width : Nat} [NeZero width] (w : BitVec width) :
    goodDimindex width → wordSemBytesInWord * w = w <<< wordShiftAmount width := by
  intro h
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm]
  congr 1
  rcases h with rfl | rfl <;> rfl

/-- Exact HOL `word_or_eq_0` (`word_gcFunctionsScript.sml:23-28`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_or_eq_0"
  (words_as_type_indexed_bitvec)]
theorem word_or_eq_0 {width : Nat} [NeZero width] (w v : BitVec width) :
    (w ||| v) = 0 ↔ w = 0 ∧ v = 0 := by
  constructor
  · intro h
    constructor <;> ext i hi
    · have := congrArg (fun x => x.getLsbD i) h
      simp at this
      simpa [BitVec.getLsbD_eq_getElem hi] using this.1
    · have := congrArg (fun x => x.getLsbD i) h
      simp at this
      simpa [BitVec.getLsbD_eq_getElem hi] using this.2
  · rintro ⟨rfl, rfl⟩
    simp

/-- Exact HOL `shift_length_has_fp_ops` (`word_gcFunctionsScript.sml:32-36`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "shift_length_has_fp_ops"]
theorem shiftLength_hasFpOps (conf : Config) (b1 b2 : Bool) :
    shiftLength { conf with hasFpOps := b1, hasFpTern := b2 } = shiftLength conf := rfl

/-- Exact HOL `ptr_to_addr_def` (`word_gcFunctionsScript.sml:42-45`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "ptr_to_addr_def"
  (words_as_type_indexed_bitvec)]
def ptrToAddr {width : Nat} [NeZero width] (conf : Config) (base w : BitVec width) :
    BitVec width :=
  base + ((w >>> shiftLength conf) * wordSemBytesInWord)

/-- Exact HOL `update_addr_def` (`word_gcFunctionsScript.sml:47-51`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "update_addr_def"
  (words_as_type_indexed_bitvec)]
def updateAddr {width : Nat} [NeZero width] (conf : Config) (fwdPtr oldAddr : BitVec width) :
    BitVec width :=
  (fwdPtr <<< shiftLength conf) ||| gcWordBitsLow (smallShiftLength conf - 1) oldAddr

/-- Exact HOL `memcpy_def` (`word_gcFunctionsScript.sml:53-59`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "memcpy_def"
  (words_as_type_indexed_bitvec)]
def memcpy {width : Nat} [NeZero width] (w a b : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    BitVec width × (BitVec width → WordLocW width) × Bool :=
  if w = 0 then (b, m, true) else
    let (b1, m1, c1) := memcpy (w - 1) (a + wordSemBytesInWord) (b + wordSemBytesInWord)
      (gcUpdate b (m a) m) dm
    (b1, m1, c1 && (dm a && dm b))
termination_by w.toNat
decreasing_by apply bitVec_toNat_sub_one_lt; assumption

theorem memcpy_zero {width : Nat} [NeZero width] (a b : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    memcpy (0#width) a b m dm = (b, m, true) := by
  rw [memcpy]; simp

theorem memcpy_of_ne {width : Nat} [NeZero width] {w : BitVec width} (h : w ≠ 0)
    (a b : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    memcpy w a b m dm =
      (let (b1, m1, c1) := memcpy (w - 1) (a + wordSemBytesInWord) (b + wordSemBytesInWord)
        (gcUpdate b (m a) m) dm
       (b1, m1, c1 && (dm a && dm b))) := by
  rw [memcpy, if_neg h]

/-- Exact HOL `decode_length_def` (`word_gcFunctionsScript.sml:61-63`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "decode_length_def"
  (words_as_type_indexed_bitvec)]
def decodeLength {width : Nat} [NeZero width] (conf : Config) (w : BitVec width) :
    BitVec width :=
  w >>> (width - conf.lenSize)

/-- Exact HOL `word_gc_move_def` (`word_gcFunctionsScript.sml:65-82`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGcMove {width : Nat} [NeZero width] (conf : Config) :
    WordLocW width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      WordLocW width × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (.loc l1 l2, i, pa, _, m, _) => (.loc l1 l2, i, pa, m, decide (l2 = 0))
  | (.word w, i, pa, old, m, dm) =>
      if w &&& 1 = 0 then (.word w, i, pa, m, true) else
        let c := dm (ptrToAddr conf old w)
        let v := m (ptrToAddr conf old w)
        if wordSemIsFwdPtr v then
          (.word (updateAddr conf (wordSemTheWord v >>> (2 : Nat)) w), i, pa, m, c)
        else
          let headerAddr := ptrToAddr conf old w
          let c := c && (dm headerAddr && wordSemIsWordLoc (m headerAddr))
          let len := decodeLength conf (wordSemTheWord (m headerAddr))
          let v := i + len + 1
          let (pa1, m1, c1) := memcpy (len + 1) headerAddr pa m dm
          let c := c && (dm headerAddr && c1)
          let m1 := gcUpdate headerAddr (.word (i <<< (2 : Nat))) m1
          (.word (updateAddr conf i w), v, pa1, m1, c)

/-- Exact HOL `word_gen_gc_partial_move_def` (`word_gcFunctionsScript.sml:84-105`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialMove {width : Nat} [NeZero width] (conf : Config) :
    WordLocW width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      WordLocW width × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (.loc l1 l2, i, pa, _, m, _, _, _) => (.loc l1 l2, i, pa, m, decide (l2 = 0))
  | (.word w, i, pa, old, m, dm, gs, rs) =>
      if w &&& 1 = 0 then (.word w, i, pa, m, true) else
        let headerAddr := ptrToAddr conf old w
        let tmp := headerAddr - old
        if tmp < gs ∨ rs ≤ tmp then
          (.word w, i, pa, m, true)
        else
          let c := dm (ptrToAddr conf old w)
          let v := m (ptrToAddr conf old w)
          if wordSemIsFwdPtr v then
            (.word (updateAddr conf (wordSemTheWord v >>> (2 : Nat)) w), i, pa, m, c)
          else
            let c := c && (dm headerAddr && wordSemIsWordLoc (m headerAddr))
            let len := decodeLength conf (wordSemTheWord (m headerAddr))
            let v := i + len + 1
            let (pa1, m1, c1) := memcpy (len + 1) headerAddr pa m dm
            let c := c && (dm headerAddr && c1)
            let m1 := gcUpdate headerAddr (.word (i <<< (2 : Nat))) m1
            (.word (updateAddr conf i w), v, pa1, m1, c)

/-- Exact HOL `word_gc_move_roots_def` (`word_gcFunctionsScript.sml:107-113`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_roots_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGcMoveRoots {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | ([], i, pa, _, m, _) => ([], i, pa, m, true)
  | (w :: ws, i, pa, old, m, dm) =>
      let (w1, i1, pa1, m1, c1) := wordGcMove conf (w, i, pa, old, m, dm)
      let (ws2, i2, pa2, m2, c2) := wordGcMoveRoots conf (ws, i1, pa1, old, m1, dm)
      (w1 :: ws2, i2, pa2, m2, c1 && c2)
termination_by x => x.1.length

/-- Exact HOL `word_gc_move_list_def` (`word_gcFunctionsScript.sml:115-123`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_list_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGcMoveList {width : Nat} [NeZero width] (conf : Config) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (a, l, i, pa, old, m, dm) =>
      if l = 0 then (a, i, pa, m, true) else
        let w := m a
        let (w1, i1, pa1, m1, c1) := wordGcMove conf (w, i, pa, old, m, dm)
        let m1 := gcUpdate a w1 m1
        let (a2, i2, pa2, m2, c2) :=
          wordGcMoveList conf (a + wordSemBytesInWord, l - 1, i1, pa1, old, m1, dm)
        (a2, i2, pa2, m2, dm a && (c1 && c2))
termination_by x => x.2.1.toNat
decreasing_by apply bitVec_toNat_sub_one_lt; assumption

theorem wordGcMoveList_zero {width : Nat} [NeZero width] (conf : Config)
    (a i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGcMoveList conf (a, 0#width, i, pa, old, m, dm) = (a, i, pa, m, true) := by
  rw [wordGcMoveList]; simp

theorem wordGcMoveList_of_ne {width : Nat} [NeZero width] (conf : Config)
    {l : BitVec width} (h : l ≠ 0) (a i pa old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    wordGcMoveList conf (a, l, i, pa, old, m, dm) =
      (let w := m a
       let (w1, i1, pa1, m1, c1) := wordGcMove conf (w, i, pa, old, m, dm)
       let m1 := gcUpdate a w1 m1
       let (a2, i2, pa2, m2, c2) :=
         wordGcMoveList conf (a + wordSemBytesInWord, l - 1, i1, pa1, old, m1, dm)
       (a2, i2, pa2, m2, dm a && (c1 && c2))) := by
  rw [wordGcMoveList, if_neg h]

/-- Exact HOL `word_gen_gc_partial_move_roots_def` (`word_gcFunctionsScript.sml:125-131`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_roots_def" (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialMoveRoots {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | ([], i, pa, _, m, _, _, _) => ([], i, pa, m, true)
  | (w :: ws, i, pa, old, m, dm, gs, rs) =>
      let (w1, i1, pa1, m1, c1) := wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs)
      let (ws2, i2, pa2, m2, c2) :=
        wordGenGcPartialMoveRoots conf (ws, i1, pa1, old, m1, dm, gs, rs)
      (w1 :: ws2, i2, pa2, m2, c1 && c2)
termination_by x => x.1.length

/-- Exact HOL `word_gen_gc_partial_move_list_def` (`word_gcFunctionsScript.sml:133-141`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_list_def" (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialMoveList {width : Nat} [NeZero width] (conf : Config) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (a, l, i, pa, old, m, dm, gs, rs) =>
      if l = 0 then (a, i, pa, m, true) else
        let w := m a
        let (w1, i1, pa1, m1, c1) := wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs)
        let m1 := gcUpdate a w1 m1
        let (a2, i2, pa2, m2, c2) := wordGenGcPartialMoveList conf
          (a + wordSemBytesInWord, l - 1, i1, pa1, old, m1, dm, gs, rs)
        (a2, i2, pa2, m2, dm a && (c1 && c2))
termination_by x => x.2.1.toNat
decreasing_by apply bitVec_toNat_sub_one_lt; assumption

/-- Exact HOL `word_gen_gc_partial_move_list_zero` (`word_gcFunctionsScript.sml:143-147`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_list_zero" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveList_zero {width : Nat} [NeZero width] (conf : Config)
    (a i pa old : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartialMoveList conf (a, 0, i, pa, old, m, dm, gs, rs) = (a, i, pa, m, true) := by
  rw [wordGenGcPartialMoveList]; simp

/-- Exact HOL `word_gen_gc_partial_move_list_suc` (`word_gcFunctionsScript.sml:149-160`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_list_suc" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveList_suc {width : Nat} [NeZero width] (conf : Config)
    (a : BitVec width) (l : Nat) (i pa old : BitVec width) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (gs rs : BitVec width) :
    wordGenGcPartialMoveList conf (a, BitVec.ofNat width (l + 1), i, pa, old, m, dm, gs, rs) =
      if BitVec.ofNat width (l + 1) = (0 : BitVec width) then (a, i, pa, m, true) else
        let w := m a
        let (w1, i1, pa1, m1, c1) := wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs)
        let m1 := gcUpdate a w1 m1
        let (a2, i2, pa2, m2, c2) := wordGenGcPartialMoveList conf
          (a + wordSemBytesInWord, BitVec.ofNat width l, i1, pa1, old, m1, dm, gs, rs)
        (a2, i2, pa2, m2, dm a && (c1 && c2)) := by
  rw [wordGenGcPartialMoveList]
  have hsub : BitVec.ofNat width (l + 1) - 1 = BitVec.ofNat width l := by
    rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  simp only [hsub]

/-- Exact HOL `word_gen_gc_partial_move_list_append`
(`word_gcFunctionsScript.sml:162-178`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_list_append" (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveList_append {width : Nat} [NeZero width] :
    ∀ (a : BitVec width) (l l' : Nat) (i pa old : BitVec width)
      (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (gs rs : BitVec width)
      (conf : Config),
      l + l' < 2 ^ width →
      wordGenGcPartialMoveList conf (a, BitVec.ofNat width (l + l'), i, pa, old, m, dm, gs, rs) =
        let (a2, i2, pa2, m2, c2) :=
          wordGenGcPartialMoveList conf (a, BitVec.ofNat width l, i, pa, old, m, dm, gs, rs)
        let (a3, i3, pa3, m3, c3) :=
          wordGenGcPartialMoveList conf (a2, BitVec.ofNat width l', i2, pa2, old, m2, dm, gs, rs)
        (a3, i3, pa3, m3, c2 && c3) := by
  intro a l
  induction l generalizing a with
  | zero =>
      intro l' i pa old m dm gs rs conf _
      rw [Nat.zero_add, show BitVec.ofNat width 0 = (0 : BitVec width) from rfl,
        wordGenGcPartialMoveList_zero]
      rcases hX : wordGenGcPartialMoveList conf (a, BitVec.ofNat width l', i, pa, old, m, dm, gs,
        rs) with ⟨a3, i3, pa3, m3, c3⟩
      simp [hX]
  | succ l ih =>
      intro l' i pa old m dm gs rs conf hlt
      have hne : BitVec.ofNat width (l + 1) ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        simp [Nat.mod_eq_of_lt (show l + 1 < 2 ^ width by omega)] at this
      have hne' : BitVec.ofNat width (l + l' + 1) ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        simp [Nat.mod_eq_of_lt (show l + l' + 1 < 2 ^ width by omega)] at this
      rw [show l + 1 + l' = (l + l') + 1 by omega, wordGenGcPartialMoveList_suc,
        wordGenGcPartialMoveList_suc]
      simp only [hne, hne', if_false]
      rw [ih _ l' _ _ _ _ _ gs rs conf (by omega)]
      cases wordGenGcPartialMove conf (m a, i, pa, old, m, dm, gs, rs) with
      | mk w1 r1 =>
        obtain ⟨i1, pa1, m1, c1⟩ := r1
        simp only
        cases wordGenGcPartialMoveList conf (a + wordSemBytesInWord, BitVec.ofNat width l, i1,
            pa1, old, gcUpdate a w1 m1, dm, gs, rs) with
        | mk a2 r2 =>
          obtain ⟨i2, pa2, m2, c2⟩ := r2
          simp only
          cases wordGenGcPartialMoveList conf (a2, BitVec.ofNat width l', i2, pa2, old, m2, dm,
              gs, rs) with
          | mk a3 r3 =>
            obtain ⟨i3, pa3, m3, c3⟩ := r3
            simp only [Bool.and_assoc]

/-- Exact HOL `word_gc_move_loop_def` (`word_gcFunctionsScript.sml:180-194`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_loop_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGcMoveLoop {width : Nat} [NeZero width] (k : Nat) (conf : Config) :
    BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × Bool →
      BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (pb, i, pa, old, m, dm, c) =>
      if pb = pa then (i, pa, m, c) else
      if k = 0 then (i, pa, m, false) else
        let w := m pb
        let c := c && (dm pb && wordSemIsWordLoc w)
        let len := decodeLength conf (wordSemTheWord w)
        if (wordSemTheWord w).getLsbD 2 then
          let pb := pb + (len + 1) * wordSemBytesInWord
          wordGcMoveLoop (k - 1) conf (pb, i, pa, old, m, dm, c)
        else
          let pb := pb + wordSemBytesInWord
          let (pb, i1, pa1, m1, c1) := wordGcMoveList conf (pb, len, i, pa, old, m, dm)
          wordGcMoveLoop (k - 1) conf (pb, i1, pa1, old, m1, dm, c && c1)
termination_by k
decreasing_by all_goals omega

/-- Exact HOL `word_full_gc_def` (`word_gcFunctionsScript.sml:196-202`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_full_gc_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordFullGc {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) ×
        (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (allRoots, new, old, m, dm) =>
      let (rs, i1, pa1, m1, c1) := wordGcMoveRoots conf (allRoots, 0, new, old, m, dm)
      let (i1, pa1, m1, c2) := wordGcMoveLoop (2 ^ width) conf (new, i1, pa1, old, m1, dm, c1)
      (rs, i1, pa1, m1, c2)

/-- Exact HOL `word_gc_fun_assum_def` (`word_gcFunctionsScript.sml:204-219`).  The
HOL `SUBSET FDOM s` of the seven-element set literal is rendered as membership of
each listed store name in the domain. -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_assum_def"
  (fmap_as_finite_support_relation := [s]) (words_as_type_indexed_bitvec)]
def wordGcFunAssum {width : Nat} [NeZero width] (conf : Config)
    (s : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  (∀ n ∈ ([.globals, .currHeap, .otherHeap, .heapLength, .triggerGC, .genStart,
      .endOfHeap] : List WordStoreHOL), (s.lookup n).isSome = true) ∧
  wordSemIsWordLoc (holFapply s .otherHeap) = true ∧
  wordSemIsWordLoc (holFapply s .currHeap) = true ∧
  wordSemIsWordLoc (holFapply s .triggerGC) = true ∧
  wordSemIsWordLoc (holFapply s .heapLength) = true ∧
  wordSemIsWordLoc (holFapply s .genStart) = true ∧
  wordSemIsWordLoc (holFapply s .endOfHeap) = true ∧
  wordSemIsWordLoc (holFapply s .globals) = true ∧
  goodDimindex width ∧
  conf.lenSize ≠ 0 ∧
  conf.lenSize + 2 < width ∧
  shiftLength conf < width

/-- Exact HOL `word_gen_gc_can_do_partial_def` (`word_gcFunctionsScript.sml:221-232`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_can_do_partial_def" (fmap_as_finite_support_relation := [s])
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcCanDoPartial {width : Nat} [NeZero width] (genSizes : List Nat)
    (s : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  genSizes ≠ [] ∧
    let allo := wordSemTheWord (holFapply s .allocSize)
    let trig := wordSemTheWord (holFapply s .triggerGC)
    let endh := wordSemTheWord (holFapply s .endOfHeap)
    allo ≤ endh - trig

/-- Exact HOL `new_trig_def` (`word_gcFunctionsScript.sml:234-243`); HOL
`byte_aligned` is the canonical `holByteAligned`. -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "new_trig_def"
  (words_as_type_indexed_bitvec)]
noncomputable def newTrig {width : Nat} [NeZero width] (heapSpace allocPref : BitVec width)
    (gs : List Nat) : BitVec width :=
  let a := allocPref.toNat
  let g := (getGenSize gs : BitVec width).toNat
  let h := heapSpace.toNat
  if a ≤ g then BitVec.ofNat width (min h g) else
  if h < a then BitVec.ofNat width h else
  if holByteAligned allocPref then allocPref else BitVec.ofNat width h

/-- Exact HOL `word_gen_gc_partial_move_ref_list_def` (`word_gcFunctionsScript.sml:252-262`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_ref_list_def" (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialMoveRefList {width : Nat} [NeZero width] (k : Nat)
    (conf : Config) :
    BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × Bool × BitVec width ×
        BitVec width × BitVec width →
      BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (pb, i, pa, old, m, dm, c, gs, rs, re) =>
      if pb = re then (i, pa, m, c) else
      if k = 0 then (i, pa, m, false) else
        let w := m pb
        let c := c && (dm pb && wordSemIsWordLoc w)
        let len := decodeLength conf (wordSemTheWord w)
        let pb := pb + wordSemBytesInWord
        let (pb, i1, pa1, m1, c1) :=
          wordGenGcPartialMoveList conf (pb, len, i, pa, old, m, dm, gs, rs)
        wordGenGcPartialMoveRefList (k - 1) conf (pb, i1, pa1, old, m1, dm, c && c1, gs, rs, re)
termination_by k
decreasing_by omega

/-- Exact HOL `word_gen_gc_partial_move_data_def` (`word_gcFunctionsScript.sml:265-285`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml"
  "word_gen_gc_partial_move_data_def" (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialMoveData {width : Nat} [NeZero width] (conf : Config)
    (k : Nat) :
    BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (h2a, i, pa, old, m, dm, gs, rs) =>
      if h2a = pa then (i, pa, m, true) else
      if k = 0 then (i, pa, m, false) else
        let c := dm h2a
        let v := m h2a
        let c := c && wordSemIsWordLoc v
        let l := decodeLength conf (wordSemTheWord v)
        if (wordSemTheWord v).getLsbD 2 then
          let h2a := h2a + (l + 1) * wordSemBytesInWord
          let (i, pa, m, c2) := wordGenGcPartialMoveData conf (k - 1) (h2a, i, pa, old, m, dm, gs, rs)
          (i, pa, m, c && c2)
        else
          let (h2a, i, pa, m, c1) := wordGenGcPartialMoveList conf
            (h2a + wordSemBytesInWord, l, i, pa, old, m, dm, gs, rs)
          let (i, pa, m, c2) := wordGenGcPartialMoveData conf (k - 1) (h2a, i, pa, old, m, dm, gs, rs)
          (i, pa, m, c && (c1 && c2))
termination_by k
decreasing_by all_goals omega

/-- Exact HOL `word_gen_gc_partial_def` (`word_gcFunctionsScript.sml:288-299`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartial {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (roots, curr, new, len, m, dm, gs, rs) =>
      let refsEnd := curr + len
      let genStart := gs >>> wordShiftAmount width
      let (roots, i, pa, m, c1) :=
        wordGenGcPartialMoveRoots conf (roots, genStart, new, curr, m, dm, gs, rs)
      let (i, pa, m, c2) := wordGenGcPartialMoveRefList (2 ^ width) conf
        (curr + rs, i, pa, curr, m, dm, c1, gs, rs, refsEnd)
      let (i, pa, m, c3) := wordGenGcPartialMoveData conf (2 ^ width)
        (new, i, pa, curr, m, dm, gs, rs)
      (roots, i, pa, m, c2 && c3)

/-- Exact HOL `word_gen_gc_partial_full_def` (`word_gcFunctionsScript.sml:301-307`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_full_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcPartialFull {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width →
      List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × Bool
  | (roots, curr, new, len, m, dm, gs, rs) =>
      let (roots, i, pa, m, c1) := wordGenGcPartial conf (roots, curr, new, len, m, dm, gs, rs)
      let cpyLength := (pa - new) >>> wordShiftAmount width
      let (b1, m, c2) := memcpy cpyLength new (curr + gs) m dm
      (roots, i, b1, m, c1 && c2)

/-- Exact HOL `is_ref_header_def` (`word_gcFunctionsScript.sml:309-311`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "is_ref_header_def"
  (words_as_type_indexed_bitvec)]
def isRefHeader {width : Nat} [NeZero width] (v : BitVec width) : Bool :=
  decide ((v &&& 0b1100) = 0b01000)

/-- Exact HOL `word_gen_gc_move_def` (`word_gcFunctionsScript.sml:313-340`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMove {width : Nat} [NeZero width] (conf : Config) :
    WordLocW width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      WordLocW width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (.loc l1 l2, i, pa, ib, pb, _, m, _) => (.loc l1 l2, i, pa, ib, pb, m, decide (l2 = 0))
  | (.word w, i, pa, ib, pb, old, m, dm) =>
      if 1 &&& w = 0 then (.word w, i, pa, ib, pb, m, true) else
        let c := dm (ptrToAddr conf old w)
        let v := m (ptrToAddr conf old w)
        let c := c && wordSemIsWordLoc v
        if wordSemIsFwdPtr v then
          (.word (updateAddr conf (wordSemTheWord v >>> (2 : Nat)) w), i, pa, ib, pb, m, c)
        else
          let headerAddr := ptrToAddr conf old w
          let c := c && (dm headerAddr && wordSemIsWordLoc (m headerAddr))
          let len := decodeLength conf (wordSemTheWord (m headerAddr))
          if isRefHeader (wordSemTheWord v) then
            let v := ib - (len + 1)
            let pb1 := pb - (len + 1) * wordSemBytesInWord
            let (_, m1, c1) := memcpy (len + 1) headerAddr pb1 m dm
            let c := c && (dm headerAddr && c1)
            let m1 := gcUpdate headerAddr (.word (v <<< (2 : Nat))) m1
            (.word (updateAddr conf v w), i, pa, v, pb1, m1, c)
          else
            let v := i + len + 1
            let (pa1, m1, c1) := memcpy (len + 1) headerAddr pa m dm
            let c := c && (dm headerAddr && c1)
            let m1 := gcUpdate headerAddr (.word (i <<< (2 : Nat))) m1
            (.word (updateAddr conf i w), v, pa1, ib, pb, m1, c)

/-- Exact HOL `word_gen_gc_move_roots_def` (`word_gcFunctionsScript.sml:342-348`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_roots_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMoveRoots {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | ([], i, pa, ib, pb, _, m, _) => ([], i, pa, ib, pb, m, true)
  | (w :: ws, i, pa, ib, pb, old, m, dm) =>
      let (w1, i1, pa1, ib, pb, m1, c1) := wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm)
      let (ws2, i2, pa2, ib, pb, m2, c2) :=
        wordGenGcMoveRoots conf (ws, i1, pa1, ib, pb, old, m1, dm)
      (w1 :: ws2, i2, pa2, ib, pb, m2, c1 && c2)
termination_by x => x.1.length

/-- Exact HOL `word_gen_gc_move_list_def` (`word_gcFunctionsScript.sml:350-358`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_list_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMoveList {width : Nat} [NeZero width] (conf : Config) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (a, l, i, pa, ib, pb, old, m, dm) =>
      if l = 0 then (a, i, pa, ib, pb, m, true) else
        let w := m a
        let (w1, i1, pa1, ib, pb, m1, c1) := wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm)
        let m1 := gcUpdate a w1 m1
        let (a2, i2, pa2, ib, pb, m2, c2) := wordGenGcMoveList conf
          (a + wordSemBytesInWord, l - 1, i1, pa1, ib, pb, old, m1, dm)
        (a2, i2, pa2, ib, pb, m2, dm a && (c1 && c2))
termination_by x => x.2.1.toNat
decreasing_by apply bitVec_toNat_sub_one_lt; assumption

/-- Exact HOL `word_gen_gc_move_data_def` (`word_gcFunctionsScript.sml:360-380`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_data_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMoveData {width : Nat} [NeZero width] (conf : Config) (k : Nat) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (h2a, i, pa, ib, pb, old, m, dm) =>
      if h2a = pa then (i, pa, ib, pb, m, true) else
      if k = 0 then (i, pa, ib, pb, m, false) else
        let c := dm h2a
        let v := m h2a
        let c := c && wordSemIsWordLoc v
        let l := decodeLength conf (wordSemTheWord v)
        if (wordSemTheWord v).getLsbD 2 then
          let h2a := h2a + (l + 1) * wordSemBytesInWord
          let (i, pa, ib, pb, m, c2) :=
            wordGenGcMoveData conf (k - 1) (h2a, i, pa, ib, pb, old, m, dm)
          (i, pa, ib, pb, m, c && c2)
        else
          let (h2a, i, pa, ib, pb, m, c1) := wordGenGcMoveList conf
            (h2a + wordSemBytesInWord, l, i, pa, ib, pb, old, m, dm)
          let (i, pa, ib, pb, m, c2) :=
            wordGenGcMoveData conf (k - 1) (h2a, i, pa, ib, pb, old, m, dm)
          (i, pa, ib, pb, m, c && (c1 && c2))
termination_by k
decreasing_by all_goals omega

/-- Exact HOL `word_gen_gc_move_refs_def` (`word_gcFunctionsScript.sml:382-396`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_refs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMoveRefs {width : Nat} [NeZero width] (conf : Config) (k : Nat) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (r2a, r1a, i, pa, ib, pb, old, m, dm) =>
      if r2a = r1a then (r2a, i, pa, ib, pb, m, true) else
      if k = 0 then (r2a, i, pa, ib, pb, m, false) else
        let c := dm r2a
        let v := m r2a
        let c := c && wordSemIsWordLoc v
        let l := decodeLength conf (wordSemTheWord v)
        let (r2a, i, pa, ib, pb, m, c1) := wordGenGcMoveList conf
          (r2a + wordSemBytesInWord, l, i, pa, ib, pb, old, m, dm)
        let (r2a, i, pa, ib, pb, m, c2) :=
          wordGenGcMoveRefs conf (k - 1) (r2a, r1a, i, pa, ib, pb, old, m, dm)
        (r2a, i, pa, ib, pb, m, c && (c1 && c2))
termination_by k
decreasing_by omega

/-- Exact HOL `word_gen_gc_move_loop_def` (`word_gcFunctionsScript.sml:398-418`).  As
in HOL, the `k = 0` result of the reference branch returns the pre-call `pb`, and
the recursive call passes it as the new `pbx`. -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_loop_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGcMoveLoop {width : Nat} [NeZero width] (conf : Config) (k : Nat) :
    BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width ×
        BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) →
      BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (pax, i, pa, ib, pb, pbx, old, m, dm) =>
      if pbx = pb then
        if pax = pa then
          (i, pa, ib, pb, m, true)
        else
          let (i, pa, ib, pb, m, c1) :=
            wordGenGcMoveData conf (2 ^ width) (pax, i, pa, ib, pb, old, m, dm)
          if k = 0 then (i, pa, ib, pb, m, false) else
            let (i, pa, ib, pb, m, c2) :=
              wordGenGcMoveLoop conf (k - 1) (pa, i, pa, ib, pb, pbx, old, m, dm)
            (i, pa, ib, pb, m, c1 && c2)
      else
        let (_pbx, i, pa, ib, pb', m, c1) :=
          wordGenGcMoveRefs conf (2 ^ width) (pb, pbx, i, pa, ib, pb, old, m, dm)
        if k = 0 then (i, pa, ib, pb, m, false) else
          let (i, pa, ib, pb, m, c2) :=
            wordGenGcMoveLoop conf (k - 1) (pax, i, pa, ib, pb', pb, old, m, dm)
          (i, pa, ib, pb, m, c1 && c2)
termination_by k
decreasing_by all_goals omega

/-- Exact HOL `word_gen_gc_def` (`word_gcFunctionsScript.sml:420-429`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGenGc {width : Nat} [NeZero width] (conf : Config) :
    List (WordLocW width) × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × (BitVec width → Bool) →
      List (WordLocW width) × BitVec width × BitVec width × BitVec width × BitVec width ×
        (BitVec width → WordLocW width) × Bool
  | (roots, curr, new, len, m, dm) =>
      let newEnd := new + len
      let len := len >>> wordShiftAmount width
      let (roots, i, pa, ib, pb, m, c1) :=
        wordGenGcMoveRoots conf (roots, 0, new, len, newEnd, curr, m, dm)
      let (i, pa, ib, pb, m, c2) :=
        wordGenGcMoveLoop conf len.toNat (new, i, pa, ib, pb, newEnd, curr, m, dm)
      (roots, i, pa, ib, pb, m, c1 && c2)

/-- Exact HOL `glob_real_def` (`word_gcFunctionsScript.sml:431-435`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "glob_real_def"
  (words_as_type_indexed_bitvec)]
def globReal {width : Nat} [NeZero width] (c : Config) (curr : BitVec width) :
    WordLocW width → WordLocW width
  | .word w => .word (curr + ((w >>> shiftLength c) <<< wordShiftAmount width))
  | w => w

open Classical in
/-- Exact HOL `word_gc_fun_def` (`word_gcFunctionsScript.sml:437-502`): the
store-level collector of `gc_fun_type`.  The store argument and result are the
canonical `HolFiniteMapExact` carrier; the type is `WordSemGcFun width` spelled
out, whose own tag records that nested finite-map translation
(`fmap_as_finite_support_function := [argument_4, result_3]`).  The finite-map
qualifiers apply only to type abbreviations or named map binders, so this
definition carries only the word qualifier. -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordGcFun {width : Nat} [NeZero width] (conf : Config) :
    (List (WordLocW width) × (BitVec width → WordLocW width) × (BitVec width → Bool) ×
        HolFiniteMapExact WordStoreHOL (WordLocW width)) →
      Option (List (WordLocW width) × (BitVec width → WordLocW width) ×
        HolFiniteMapExact WordStoreHOL (WordLocW width)) :=
  fun (roots, m, dm, s) =>
    let c1 := wordGcFunAssum conf s
    let new := wordSemTheWord (holFapply s .otherHeap)
    let old := wordSemTheWord (holFapply s .currHeap)
    let len := wordSemTheWord (holFapply s .heapLength)
    let allRoots := holFapply s .globals :: roots
    match conf.gcKind with
    | .none =>
        let s1 := s.updateListEq [(.nextFree, .word old), (.triggerGC, .word old),
          (.endOfHeap, .word old)]
        if c1 then some (roots, m, s1) else none
    | .simple =>
        let (roots1, _i1, pa1, m1, c2) := wordFullGc conf (allRoots, new, old, m, dm)
        let s1 := s.updateListEq [(.currHeap, .word new), (.otherHeap, .word old),
          (.nextFree, .word pa1), (.triggerGC, .word (new + len)),
          (.endOfHeap, .word (new + len)), (.globals, holHd roots1),
          (.globReal, globReal conf new (holHd roots1))]
        if c1 ∧ c2 = true then some (roots1.tail, m1, s1) else none
    | .generational genSizes =>
        if ¬c1 then none else
        if wordGenGcCanDoPartial genSizes s then
          let gs := wordSemTheWord (holFapply s .genStart)
          let rs := wordSemTheWord (holFapply s .endOfHeap) - wordSemTheWord (holFapply s .currHeap)
          let len := wordSemTheWord (holFapply s .heapLength)
          let endh := wordSemTheWord (holFapply s .endOfHeap)
          let (roots1, _i1, pa1, m1, c2) :=
            wordGenGcPartialFull conf (allRoots, old, new, len, m, dm, gs, rs)
          let a := wordSemTheWord (holFapply s .allocSize)
          let s1 := s.updateListEq [(.currHeap, .word old), (.otherHeap, .word new),
            (.nextFree, .word pa1), (.genStart, .word (pa1 - old)),
            (.triggerGC, .word (pa1 + newTrig (endh - pa1) a genSizes)),
            (.globals, holHd roots1), (.globReal, globReal conf old (holHd roots1)),
            (.temp 0, .word 0), (.temp 1, .word 0)]
          let c3 := a ≤ endh - pa1 ∧ a ≤ newTrig (endh - pa1) a genSizes
          if c2 = true ∧ c3 then some (roots1.tail, m1, s1) else none
        else
          let (roots1, _i1, pa1, _ib1, pb1, m1, c2) :=
            wordGenGc conf (allRoots, old, new, len, m, dm)
          let a := wordSemTheWord (holFapply s .allocSize)
          let s1 := s.updateListEq [(.currHeap, .word new), (.otherHeap, .word old),
            (.nextFree, .word pa1), (.genStart, .word (pa1 - new)),
            (.triggerGC, .word (pa1 + newTrig (pb1 - pa1) a genSizes)),
            (.endOfHeap, .word pb1), (.globals, holHd roots1),
            (.globReal, globReal conf new (holHd roots1)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.temp 2, .word 0), (.temp 3, .word 0),
            (.temp 4, .word 0), (.temp 5, .word 0), (.temp 6, .word 0)]
          if c2 = true then some (roots1.tail, m1, s1) else none

@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "refs_to_addresses_def"]
def refs_to_addresses {α β : Type} : List (HeapElement α β) → List (HeapAddress α)
  | [] => []
  | .dataElement ptrs _ _ :: refs => ptrs ++ refs_to_addresses refs
  | _ :: refs => refs_to_addresses refs

end Flapjack.Compiler.Backend.WordGcFunctions
