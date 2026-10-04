import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedSSA
import Flapjack.Pancake.Proofs.WordConvs.Unreach
import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
import Flapjack.Pancake.Proofs.WordConvs.WordAlloc
import Flapjack.Pancake.Proofs.WordConvs.WordCse
import Flapjack.Pancake.Proofs.WordConvs.CopyProp
import Flapjack.Compiler.Backend.WordToWord.Compile

/-!
# `wordConvsProof`: `not_created_subprogs` through `compile_single`

`three_to_two_reg_prog_not_created_subprogs` (2204-2213), the `remove_unreach`
group (2402-2434) and `compile_single_not_created_subprogs` (2972-2989) of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml`. HOL's free
predicate `P` is the leading binder.
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Backend.WordUnreach

variable {width : Nat} [NeZero width]

/-- HOL `three_to_two_reg_prog_not_created_subprogs` (`wordConvsProofScript.sml:2204-2213`);
    HOL's free flag `b` follows `P`. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "three_to_two_reg_prog_not_created_subprogs" (words_as_type_indexed_bitvec)]
theorem notCreated_threeToTwoRegProg {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) (b : Bool) :
    ∀ prog : WordLangProgHOL (BitVec width), notCreatedSubprogsHOL P prog = true →
      notCreatedSubprogsHOL P (threeToTwoRegProg b prog) = true := by
  intro program source
  cases b <;> simp [threeToTwoRegProg, source]
  induction program using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases threeToTwoReg program <;> simp_all +zetaDelta [notCreatedSubprogsHOL]
    all_goals
      repeat' first
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta [notCreatedSubprogsHOL]
        | split
        | constructor

/-- Flapjack factoring of the descriptor analysis for the `SimpSeq` proof; HOL has
    no separately named descriptor theorem. -/
private theorem notCreated_ofDestSeqMove (P : WordLangProgHOL (BitVec width) → Bool)
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : notCreatedSubprogsHOL P program = true) :
    notCreatedSubprogsHOL P rest = true := by
  cases program <;> simp_all [destSeqMove, notCreatedSubprogsHOL]
  case move =>
    rw [← descriptor.2.2]
    simp [notCreatedSubprogsHOL]
  case seq first second =>
    cases first <;> simp_all [notCreatedSubprogsHOL]

/-- HOL `SimpSeq_not_created_subprogs` (`wordConvsProofScript.sml:2402-2411`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "SimpSeq_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_simpSeq {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (ps qs : WordLangProgHOL (BitVec width))
    (h : notCreatedSubprogsHOL P ps = true ∧ notCreatedSubprogsHOL P qs = true) :
    notCreatedSubprogsHOL P (simpSeq ps qs) = true := by
  obtain ⟨firstValid, secondValid⟩ := h
  fun_cases simpSeq ps qs <;> simp_all +zetaDelta [notCreatedSubprogsHOL]
  all_goals apply notCreated_ofDestSeqMove P qs <;> assumption

/-- HOL `Seq_assoc_right_not_created_subprogs` (`wordConvsProofScript.sml:2413-2425`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "Seq_assoc_right_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_seqAssocRight {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (ps qs : WordLangProgHOL (BitVec width))
    (h : notCreatedSubprogsHOL P ps = true ∧ notCreatedSubprogsHOL P qs = true) :
    notCreatedSubprogsHOL P (seqAssocRight ps qs) = true := by
  obtain ⟨firstValid, secondValid⟩ := h
  induction ps using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing qs with
  | h first ih =>
    fun_cases seqAssocRight first qs <;> try simp_all +zetaDelta only [notCreatedSubprogsHOL]
    all_goals
      repeat' first
        | (apply notCreated_simpSeq; constructor)
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [notCreatedSubprogsHOL, Bool.and_eq_true]
        | split
        | constructor

/-- HOL `remove_unreach_not_created_subprogs` (`wordConvsProofScript.sml:2427-2434`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_unreach_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_removeUnreach {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (removeUnreach prog) = true :=
  fun h => notCreated_seqAssocRight P prog .skip ⟨h, rfl⟩

/-- HOL `compile_single_not_created_subprogs` (`wordConvsProofScript.sml:2972-2990`); HOL's free
    `two_reg_arith reg_count alg c prog_opt` follow `P`. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_single_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem compile_single_not_created_subprogs {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (twoRegArith : Bool) (regCount alg : Nat) (c : Compiler.Encoders.Asm.AsmConfigExact width)
    (progOpt : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    notCreatedSubprogsHOL P progOpt.1.2.2 = true →
    notCreatedSubprogsHOL P (Compiler.Backend.WordToWord.compileSingle twoRegArith regCount alg c progOpt).2.2 =
      true := by
  rcases progOpt with ⟨⟨n, ar, prog⟩, col⟩
  intro h
  apply wordAlloc_notCreatedSubprogs
  apply removeDeadProg_notCreatedSubprogs
  apply notCreated_removeUnreach
  apply notCreated_threeToTwoRegProg
  apply copy_prop_not_created_subprogs
  apply word_common_subexp_elim_not_created_subprogs
  apply removeDeadProg_notCreatedSubprogs
  apply notCreated_fullSsaCcTrans
  apply notCreated_instSelect
  exact notCreated_compileExp P prog h

end Flapjack.WordConvs
