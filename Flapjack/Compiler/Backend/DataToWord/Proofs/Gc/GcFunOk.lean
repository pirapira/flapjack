import Flapjack.Compiler.Backend.WordGcFunctions.Roots
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcFunOk
import Flapjack.FiniteMap.MapKeys

/-! `gc_fun_ok_word_gc_fun` (`data_to_word_gcProofScript.sml:6419-6437`): the word
garbage collector satisfies the GC callback contract. The collector reads the
store only at keys other than `Handler` and writes it only through
`FUPDATE_LIST` at keys other than `Handler`, so running it on `s \\ Handler`
and restoring `Handler` gives the run on `s`. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Pancake

section Support
variable {width : Nat} [NeZero width]

theorem holFapply_eraseEq_handler {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} {k : WordStoreHOL} (hk : k ≠ .handler) :
    holFapply (s.eraseEq .handler) k = holFapply s k := by
  simp [holFapply, FDOMSUB_HOL, hk]

theorem fupdateList_agree {L : List (WordStoreHOL × WordLocW width)} :
    ∀ (f g : FiniteMap WordStoreHOL (WordLocW width)), (∀ k, k ≠ .handler → f k = g k) →
      ∀ k, k ≠ .handler → FUPDATE_LIST_HOL f L k = FUPDATE_LIST_HOL g L k := by
  induction L with
  | nil => intro f g h k hk; exact h k hk
  | cons e L ih =>
    intro f g h k hk
    simp only [FUPDATE_LIST_HOL_cons]
    refine ih _ _ ?_ k hk
    intro k' hk'
    simp only [FUPDATE_HOL]
    split
    · rfl
    · exact h k' hk'

/-- Restoring `Handler` after a `Handler`-free list update of `s \\ Handler`. -/
theorem updateListEq_eraseHandler {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} {v : WordLocW width}
    (hv : s.lookup .handler = some v) {L : List (WordStoreHOL × WordLocW width)}
    (hL : WordStore.handler ∉ L.map Prod.fst) :
    s.updateListEq L = ((s.eraseEq .handler).updateListEq L).updateEq (.handler, v) := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  simp only [HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.lookup_updateEq]
  by_cases hk : k = .handler
  · subst hk
    have := FLOOKUP_FUPDATE_LIST_HOL_not_mem s.lookup L .handler hL
    simp only [FLOOKUP] at this
    simp [FUPDATE_HOL, this, hv]
  · simp only [FUPDATE_HOL, hk, if_false]
    exact fupdateList_agree _ _ (fun k' hk' => by simp [FDOMSUB_HOL, hk']) k hk

theorem lookup_handler_updateListEq_erase {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} {L : List (WordStoreHOL × WordLocW width)}
    (hL : WordStore.handler ∉ L.map Prod.fst) :
    ((s.eraseEq .handler).updateListEq L).lookup .handler = none := by
  have := FLOOKUP_FUPDATE_LIST_HOL_not_mem (s.eraseEq .handler).lookup L .handler hL
  simp only [FLOOKUP] at this
  simp [this, FDOMSUB_HOL]

theorem wordGcFunAssum_eraseHandler {c : Config} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    wordGcFunAssum c (s.eraseEq .handler) = wordGcFunAssum c s := by
  simp [wordGcFunAssum, holFapply_eraseEq_handler, FDOMSUB_HOL]

theorem wordGenGcCanDoPartial_eraseHandler {g : List Nat} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)} :
    wordGenGcCanDoPartial g (s.eraseEq .handler) = wordGenGcCanDoPartial g s := by
  simp [wordGenGcCanDoPartial, holFapply_eraseEq_handler]

theorem wordGcFun_eraseHandler {c : Config} {wl : List (WordLocW width)}
    {m : BitVec width → WordLocW width} {d : BitVec width → Bool} {s : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    {v : WordLocW width} (hv : s.lookup .handler = some v) :
    wordGcFun c (wl, m, d, s) = (wordGcFun c (wl, m, d, s.eraseEq .handler)).map
      (fun r => (r.1, r.2.1, r.2.2.updateEq (.handler, v))) := by
  simp only [wordGcFun, wordGcFunAssum_eraseHandler, wordGenGcCanDoPartial_eraseHandler,
    holFapply_eraseEq_handler (by simp : WordStore.otherHeap ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.currHeap ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.heapLength ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.globals ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.genStart ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.endOfHeap ≠ .handler),
    holFapply_eraseEq_handler (by simp : WordStore.allocSize ≠ .handler)]
  split
  · by_cases hA : wordGcFunAssum c s <;>
      simp_all [wordGcFunAssum_eraseHandler, updateListEq_eraseHandler hv]
  · by_cases hA : wordGcFunAssum c s <;>
      simp_all [wordGcFunAssum_eraseHandler, holFapply_eraseEq_handler, updateListEq_eraseHandler hv]
  · rename_i g _
    by_cases hA : wordGcFunAssum c s <;> by_cases hP : wordGenGcCanDoPartial g s <;>
      simp_all [wordGcFunAssum_eraseHandler, wordGenGcCanDoPartial_eraseHandler,
        updateListEq_eraseHandler hv]

/-- The collector's output store has no `Handler` when its input has none. -/
theorem wordGcFun_handler_none {c : Config} {wl wl1 : List (WordLocW width)}
    {m m1 : BitVec width → WordLocW width} {d : BitVec width → Bool}
    {s s1 : HolFiniteMapExact WordStoreHOL (WordLocW width)}
    (h : wordGcFun c (wl, m, d, s.eraseEq .handler) = some (wl1, m1, s1)) :
    s1.lookup .handler = none := by
  simp only [wordGcFun] at h
  split at h <;> (repeat' split at h) <;>
    first
      | (simp at h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨-, -, rfl⟩ := h
         exact lookup_handler_updateListEq_erase (by simp))

end Support

/-- HOL `gc_fun_ok_word_gc_fun`. HOL's free `c1` is implicit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_fun_ok_word_gc_fun"
  (words_as_type_indexed_bitvec)]
theorem gcFunOkWordGcFun {width : Nat} [NeZero width] {c1 : Config} :
    wordGcFunOk (wordGcFun c1 : List (WordLocW width) × (BitVec width → WordLocW width) × _ → _) := by
  rintro wl m d s wl1 m1 s1 ⟨hH, hf⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hH
  refine ⟨word_gc_fun_LENGTH hf, wordGcFun_handler_none hf, ?_⟩
  rw [wordGcFun_eraseHandler hv, hf, hv]
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
