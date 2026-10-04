import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.Proofs.NoFP
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoMtCode

/-!
# `loop_to_wordProof`: no_install/no_alloc/no_mt lemmas

The `(*** no_install/no_alloc/no_mt lemmas ***)` section of
`cakeml/pancake/proofs/loop_to_wordProofScript.sml` (1909-1997): `comp` only
creates `ShareInst`, `Call` and `LocValue` among the nodes `not_created_subprogs`
inspects, so the compiled code has no `Install`, `Alloc` or `MustTerminate`.
HOL's side condition `∀x. (case x of ShareInst _ _ _ => T | Call _ _ _ _ => T |
LocValue _ _ => T | _ => F) ⇒ P x` is the Boolean `match` below; HOL's `EVERY`
over a list is `∀ x ∈ l`.
-/

namespace Flapjack.LoopToWord
open Flapjack Flapjack.WordProps

/-- HOL `loop_to_word_comp_not_created` (`loop_to_wordProofScript.sml:1911-1925`); HOL's free
    predicate `P` is the leading binder. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_not_created"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_not_created {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    (∀ x : WordLangProgHOL (BitVec width), (match x with
      | .shareInst _ _ _ => true
      | .call _ _ _ _ => true
      | .locValue _ _ => true
      | _ => false) = true → P x = true) →
    ∀ (ctxt : Spt Nat) (prog : HolLoopProg width) (l : Nat × Nat)
      (wprog : WordLangProgHOL (BitVec width)) (l2 : Nat × Nat),
      compHOL ctxt prog l = (wprog, l2) → notCreatedSubprogsHOL P wprog = true := by
  intro hP ctxt prog l wprog l2 hc
  rw [show wprog = (compHOL ctxt prog l).1 by rw [hc]]
  clear hc wprog l2
  induction prog using (measure (fun p : HolLoopProg width => sizeOf p)).wf.induction
      generalizing l with
  | h prog ih =>
    have pc : ∀ r (o : Option Nat) (a : List Nat) h,
        P (.call r o a h : WordLangProgHOL (BitVec width)) = true :=
      fun _ _ _ _ => hP _ rfl
    have ps : ∀ op v (e : WordLangExpHOL (BitVec width)), P (.shareInst op v e) = true :=
      fun _ _ _ => hP _ rfl
    have pl : ∀ a b, P (.locValue a b : WordLangProgHOL (BitVec width)) = true :=
      fun _ _ => hP _ rfl
    have sub : ∀ q, sizeOf q < sizeOf prog → ∀ l, notCreatedSubprogsHOL P (compHOL ctxt q l).1 = true :=
      fun q hq l => ih q hq l
    have sub' : ∀ q lab w lab', compHOL ctxt q lab = (w, lab') → sizeOf q < sizeOf prog →
        notCreatedSubprogsHOL P w = true := by
      intro q lab w lab' h hq
      have := sub q hq lab
      rw [h] at this
      exact this
    fun_cases compHOL ctxt prog l <;>
      (try simp +zetaDelta only [notCreatedSubprogsHOL, Bool.and_eq_true, pc, ps, pl, true_and,
        and_true])
    all_goals
      repeat' first
        | rfl
        | constructor
        | (apply sub; simp)
        | (exact sub' _ _ _ _ ‹_› (by simp; omega))

/-- HOL `loop_to_word_comp_func_not_created` (`loop_to_wordProofScript.sml:1927-1938`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_func_not_created"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_func_not_created {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    (∀ x : WordLangProgHOL (BitVec width), (match x with
      | .shareInst _ _ _ => true
      | .call _ _ _ _ => true
      | .locValue _ _ => true
      | _ => false) = true → P x = true) →
    ∀ (body : HolLoopProg width) (name : Nat) (params : List Nat),
      notCreatedSubprogsHOL P (loopToWordCompFuncHOL name params body) = true := by
  intro hP body name params
  exact loop_to_word_comp_not_created P hP _ body _ _ _ rfl

/-- HOL `loop_to_word_compile_not_created` (`loop_to_wordProofScript.sml:1940-1950`); HOL's
    `EVERY` is `∀ x ∈ l` and `SND o SND` is `fun e => e.2.2`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_not_created"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_not_created {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (panProg : List (Nat × List Nat × HolLoopProg width)),
      (∀ x : WordLangProgHOL (BitVec width), (match x with
        | .shareInst _ _ _ => true
        | .call _ _ _ _ => true
        | .locValue _ _ => true
        | _ => false) = true → P x = true) →
      ∀ x ∈ (loopToWordCompileProgHOL panProg).map (fun e => e.2.2),
        notCreatedSubprogsHOL P x = true := by
  intro panProg hP x hx
  simp only [loopToWordCompileProgHOL, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨e, -, rfl⟩ := hx
  exact loop_to_word_comp_func_not_created P hP _ _ _

/-- HOL `loop_to_word_compile_not_created_MEM` (`loop_to_wordProofScript.sml:1952-1963`,
    `[local]`); HOL's free `a b p pan_prog P` are explicit. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_not_created_MEM"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_not_created_MEM {width : Nat} [NeZero width] (a b : Nat)
    (p : WordLangProgHOL (BitVec width)) (panProg : List (Nat × List Nat × HolLoopProg width))
    (P : WordLangProgHOL (BitVec width) → Bool) :
    (a, b, p) ∈ loopToWordCompileProgHOL panProg →
    (∀ x : WordLangProgHOL (BitVec width), (match x with
      | .shareInst _ _ _ => true
      | .call _ _ _ _ => true
      | .locValue _ _ => true
      | _ => false) = true → P x = true) →
    notCreatedSubprogsHOL P p = true := by
  intro hmem hP
  exact loop_to_word_compile_not_created P panProg hP p
    (List.mem_map.mpr ⟨(a, b, p), hmem, rfl⟩)

/-- The compiled code of `loop_to_word$compile` satisfies `not_created_subprogs` for every
    predicate holding on `ShareInst`, `Call` and `LocValue` (Flapjack factoring of the
    common step of HOL's three `loop_compile_no_*_code` proofs). -/
theorem loopCompile_lookup_notCreated {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool)
    (hP : ∀ x : WordLangProgHOL (BitVec width), (match x with
      | .shareInst _ _ _ => true
      | .call _ _ _ _ => true
      | .locValue _ _ => true
      | _ => false) = true → P x = true)
    (prog : List (Nat × List Nat × HolLoopProg width)) (k n : Nat) (p : WordLangProgHOL (BitVec width))
    (h : sptLookup k (sptFromAList (loopToWordCompileHOL prog)) = some (n, p)) :
    notCreatedSubprogsHOL P p = true := by
  rw [sptLookup_sptFromAList] at h
  exact loop_to_word_compile_not_created_MEM k n p prog P (sptAListLookup_mem _ _ _ h) hP

/-- HOL `loop_compile_no_install_code` (`loop_to_wordProofScript.sml:1966-1975`); HOL's free
    `prog` is explicit. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_compile_no_install_code"
  (words_as_type_indexed_bitvec)]
theorem loop_compile_no_install_code {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width)) :
    noInstallCode (sptFromAList (loopToWordCompileHOL prog)) := by
  intro k n p h
  rw [noInstallSubprogsHOL_eq_notCreated]
  refine loopCompile_lookup_notCreated _ ?_ prog k n p h
  intro x hx
  cases x <;> simp at hx ⊢

/-- HOL `loop_compile_no_alloc_code` (`loop_to_wordProofScript.sml:1977-1986`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_compile_no_alloc_code"
  (words_as_type_indexed_bitvec)]
theorem loop_compile_no_alloc_code {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width)) :
    noAllocCode (sptFromAList (loopToWordCompileHOL prog)) := by
  intro k n p h
  rw [noAllocSubprogsHOL_eq_notCreated]
  refine loopCompile_lookup_notCreated _ ?_ prog k n p h
  intro x hx
  cases x <;> simp at hx ⊢

/-- HOL `loop_compile_no_mt_code` (`loop_to_wordProofScript.sml:1988-1997`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_compile_no_mt_code"
  (words_as_type_indexed_bitvec)]
theorem loop_compile_no_mt_code {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width)) :
    noMtCode (sptFromAList (loopToWordCompileHOL prog)) := by
  intro k n p h
  rw [noMtSubprogsHOL_eq_notCreated]
  refine loopCompile_lookup_notCreated _ ?_ prog k n p h
  intro x hx
  cases x <;> simp at hx ⊢

end Flapjack.LoopToWord
