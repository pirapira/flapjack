import Flapjack.Compiler.Backend.WordGcFunctions.Roots
import Flapjack.Compiler.Backend.WordSimp.Proofs.ConstFpLemmas

/-! `gc_fun_const_ok_word_gc_fun` (`data_to_word_gcProofScript.sml:6409-6417`): the word
garbage collector keeps every GC-constant root, as `word_gc_IMP_EVERY2` gives. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Pancake

/-- HOL `gc_fun_const_ok_word_gc_fun` (`data_to_word_gcProofScript.sml:6409-6417`). HOL's free
    `c` is implicit; the type ascription on `wordGcFun` only fixes the word width. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_fun_const_ok_word_gc_fun"
  (words_as_type_indexed_bitvec)]
theorem gcFunConstOkWordGcFun {width : Nat} [NeZero width] {c : Config} :
    WordSimp.gcFunConstOk
      (wordGcFun c : List (WordLocW width) × (BitVec width → WordLocW width) × _ → _) := by
  rintro ⟨xs, m, dm, st⟩ ⟨ys, m1, s1⟩ h
  have hrel := word_gc_IMP_EVERY2 h
  dsimp only
  clear h
  induction hrel with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (fun hc => (hab.2 hc).symm) ih

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
