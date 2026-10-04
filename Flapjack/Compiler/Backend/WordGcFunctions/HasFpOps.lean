import Flapjack.Compiler.Backend.WordGcFunctions

/-! The `has_fp_ops` lemmas of `word_gcFunctionsScript.sml:598-792`: every GC
function ignores the floating-point capability flags of the data configuration.
Each proof is a kernel definitional-equality check: the functions read the
configuration only through fields other than `hasFpOps`/`hasFpTern`. -/

namespace Flapjack.Compiler.Backend.WordGcFunctions

open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Exact HOL `word_gc_fun_assum_has_fp_ops` (`word_gcFunctionsScript.sml:599-604`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_assum_has_fp_ops"
  (fmap_as_finite_support_relation := [s]) (words_as_type_indexed_bitvec)]
theorem wordGcFunAssum_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool}
    {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    wordGcFunAssum { conf with hasFpOps := b1, hasFpTern := b2 } s = wordGcFunAssum conf s := by
  with_unfolding_all rfl

/-- Exact HOL `word_gc_move_has_fp_ops` (`word_gcFunctionsScript.sml:606-613`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGcMove_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : WordLocW width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool),
      wordGcMove { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGcMove conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_has_fp_ops` (`word_gcFunctionsScript.sml:615-622`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : WordLocW width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool),
      wordGenGcMove { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcMove conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_move_has_fp_ops` (`word_gcFunctionsScript.sml:624-631`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMove_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : WordLocW width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width,
      wordGenGcPartialMove { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcPartialMove conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gc_move_list_has_fp_ops` (`word_gcFunctionsScript.sml:633-641`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_list_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveList_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGcMoveList { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGcMoveList conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_list_has_fp_ops` (`word_gcFunctionsScript.sml:643-651`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_list_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveList_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGenGcMoveList { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcMoveList conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_move_list_has_fp_ops` (`word_gcFunctionsScript.sml:653-661`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_list_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveList_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width),
      wordGenGcPartialMoveList { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcPartialMoveList conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gc_move_roots_has_fp_ops` (`word_gcFunctionsScript.sml:663-671`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_roots_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveRoots_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : List (WordLocW width) × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGcMoveRoots { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGcMoveRoots conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_roots_has_fp_ops` (`word_gcFunctionsScript.sml:673-681`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_roots_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRoots_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : List (WordLocW width) × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGenGcMoveRoots { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcMoveRoots conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_move_roots_has_fp_ops` (`word_gcFunctionsScript.sml:683-691`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_roots_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRoots_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (conf : Config) (x : List (WordLocW width) × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width),
      wordGenGcPartialMoveRoots { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcPartialMoveRoots conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gc_move_loop_has_fp_ops` (`word_gcFunctionsScript.sml:693-701`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_loop_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveLoop_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × Bool),
      wordGcMoveLoop n { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGcMoveLoop n conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_move_data_has_fp_ops` (`word_gcFunctionsScript.sml:703-711`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_data_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveData_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width),
      wordGenGcPartialMoveData { conf with hasFpOps := b1, hasFpTern := b2 } n x = wordGenGcPartialMoveData conf n x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_data_has_fp_ops` (`word_gcFunctionsScript.sml:713-721`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_data_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveData_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGenGcMoveData { conf with hasFpOps := b1, hasFpTern := b2 } n x = wordGenGcMoveData conf n x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_refs_has_fp_ops` (`word_gcFunctionsScript.sml:723-731`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_refs_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRefs_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGenGcMoveRefs { conf with hasFpOps := b1, hasFpTern := b2 } n x = wordGenGcMoveRefs conf n x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_move_ref_list_has_fp_ops` (`word_gcFunctionsScript.sml:733-741`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_ref_list_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRefList_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × Bool × BitVec width × BitVec width × BitVec width),
      wordGenGcPartialMoveRefList n { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcPartialMoveRefList n conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_move_loop_has_fp_ops` (`word_gcFunctionsScript.sml:743-751`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_loop_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveLoop_hasFpOps {width : Nat} [NeZero width] {b1 b2 : Bool} :
    ∀ (n : Nat) (conf : Config) (x : BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool)),
      wordGenGcMoveLoop { conf with hasFpOps := b1, hasFpTern := b2 } n x = wordGenGcMoveLoop conf n x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_full_gc_has_fp_ops` (`word_gcFunctionsScript.sml:753-759`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_full_gc_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordFullGc_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : List (WordLocW width) × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool),
      wordFullGc { conf with hasFpOps := b1, hasFpTern := b2 } x = wordFullGc conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_partial_full_has_fp_ops` (`word_gcFunctionsScript.sml:761-768`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_full_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialFull_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : List (WordLocW width) × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool) × BitVec width × BitVec width,
      wordGenGcPartialFull { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGcPartialFull conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `word_gen_gc_has_fp_ops` (`word_gcFunctionsScript.sml:770-777`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGenGc_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    ∀ x : List (WordLocW width) × BitVec width × BitVec width × BitVec width × (BitVec width → WordLocW width) × (BitVec width → Bool),
      wordGenGc { conf with hasFpOps := b1, hasFpTern := b2 } x = wordGenGc conf x := by
  intros
  with_unfolding_all rfl

/-- Exact HOL `glob_real_has_fp_ops` (`word_gcFunctionsScript.sml:779-784`). -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "glob_real_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem globReal_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool}
    {x : BitVec width} {y : WordLocW width} :
    globReal { conf with hasFpOps := b1, hasFpTern := b2 } x y = globReal conf x y := by
  with_unfolding_all rfl

/-- Exact HOL `word_gc_fun_has_fp_ops` (`word_gcFunctionsScript.sml:786-791`):
an equation between functions, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_has_fp_ops"
  (words_as_type_indexed_bitvec)]
theorem wordGcFun_hasFpOps {width : Nat} [NeZero width] {conf : Config} {b1 b2 : Bool} :
    (wordGcFun : Config → List (WordLocW width) × (BitVec width → WordLocW width) × _ → _)
        { conf with hasFpOps := b1, hasFpTern := b2 } = wordGcFun conf := by
  with_unfolding_all rfl

end Flapjack.Compiler.Backend.WordGcFunctions
