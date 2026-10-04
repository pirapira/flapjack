import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Pancake.WordConvs
-- Reuse matcher congruence helpers from the accepted proof modules.
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Sequence
import Mathlib.Tactic

/-!
Instruction-predicate preservation for the exact native WordSimp pipeline.
The original `every_inst` predicate is arbitrary: the proofs inspect syntax,
not the interpretation of integer or floating-point instructions. Native calls
without a return retain HOL's vacuous predicate even when a handler is present.
This group supplies the original `compile_exp_no_inst` prerequisite of
`word_to_wordProof$compile_to_word_conventions`; it does not prove that enclosing
convention theorem or whole compiler correctness.
-/

namespace Flapjack.WordConvs.WordSimpInstructions
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Smart sequencing preserves exactly the conjunction of the two source predicates. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_SmartSeq"
  (words_as_type_indexed_bitvec)]
theorem everyInstSmartSeq {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (p q : WordLangProgHOL (BitVec width)) :
    everyInst P (smartSeqHOL p q) = (everyInst P p && everyInst P q) := by
  cases p <;> simp [smartSeqHOL, everyInst]

/-- Both actual sequence-destructor components satisfy the source instruction predicate. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "dest_Seq_no_inst"
  (words_as_type_indexed_bitvec)]
theorem destSeqNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) :
    everyInst P (destSeq program).1 = true ∧ everyInst P (destSeq program).2 = true := by
  cases program <;> simp_all [destSeq, everyInst]

/-- Sequence association preserves the two original source predicates, including all recursive handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "Seq_assoc_no_inst"
  (words_as_type_indexed_bitvec)]
theorem seqAssocNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool)
    (first second : WordLangProgHOL (BitVec width))
    (source : everyInst P first = true ∧ everyInst P second = true) :
    everyInst P (seqAssoc first second) = true := by
  induction second using (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction generalizing first with
  | h second ih =>
    fun_cases seqAssoc first second <;>
      simp_all +zetaDelta [everyInstSmartSeq, everyInst]
    all_goals repeat' first
      | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
      | assumption
      | constructor
      | split
      | simp_all [everyInst]

/-- Constant materialization adds only assignments, so the arbitrary instruction predicate is unchanged. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_drop_consts"
  (words_as_type_indexed_bitvec)]
theorem everyInstDropConsts {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (cs : Spt (BitVec width))
    (names : List Nat) (program : WordLangProgHOL (BitVec width)) :
    everyInst P (smartSeqHOL (dropConsts cs names) program) = everyInst P program := by
  have harmless : everyInst P (dropConsts cs names) = true := by
    induction names with
    | nil => rfl
    | cons n ns ih => cases h : sptLookup n cs <;> simp [dropConsts, h, everyInstSmartSeq, everyInst, ih]
  simp [everyInstSmartSeq, harmless]

/-- Flapjack-only generalized induction support for arbitrary incoming constant maps. The original every_inst_const_fp proof generalizes the loop internally; it does not name a separate theorem with this signature. -/
private theorem constFpLoopNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (cs : Spt (BitVec width))
    (source : everyInst P program = true) :
    everyInst P (constFpLoop program cs).1 = true := by
  induction program using (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction generalizing cs with
  | h program ih =>
    have advance (p : WordLangProgHOL (BitVec width)) (state : Spt (BitVec width))
        (out : WordLangProgHOL (BitVec width)) (outState : Spt (BitVec width))
        (run : constFpLoop p state = (out, outState))
        (smaller : sizeOf p < sizeOf program) (input : everyInst P p = true) :
        everyInst P out = true := by
      simpa only [run] using ih p smaller state input
    fun_cases constFpLoop program cs <;>
      simp_all +zetaDelta [everyInstDropConsts, everyInst]
    all_goals repeat' first
      | assumption
      | exact source.1
      | exact source.2
      | omega
      | (change sizeOf _ < sizeOf _; simp; omega)
      | apply And.intro
      | apply ih
      | (apply advance; assumption)
    all_goals change sizeOf _ < sizeOf _
    all_goals simp

/-- Constant folding preserves every original instruction predicate through the actual native state-threading loop. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_const_fp"
  (words_as_type_indexed_bitvec)]
theorem everyInstConstFp {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) :
    everyInst P (constFp program) = true :=
  constFpLoopNoInst P program .ln source

/-- Successful hoisting preserves the three original source predicates. The dummy is unrestricted; the unused HOL variable s retains an independent arbitrary carrier. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "try_if_hoist2_no_inst"
  (words_as_type_indexed_bitvec)]
theorem tryIfHoist2NoInst {width : Nat} [NeZero width] {δ : Type}
    (P : WordLangInst (BitVec width) → Bool) (n : Nat)
    (first interm dummy second out : WordLangProgHOL (BitVec width)) (_s : δ)
    (run : tryIfHoist2 n first interm dummy second = some out)
    (firstValid : everyInst P first = true) (intermValid : everyInst P interm = true)
    (secondValid : everyInst P second = true) : everyInst P out = true := by
  have destIfEqSome (program : WordLangProgHOL (BitVec width)) (cmp : Cmp) (lhs : Nat)
      (rhs : WordRegImm (BitVec width)) (left right : WordLangProgHOL (BitVec width)) :
      destIf program = some (cmp, lhs, rhs, left, right) ↔
        program = .ite cmp lhs rhs left right := by
    cases program <;> simp [destIf]
  induction n generalizing first interm dummy second out with
  | zero => simp [tryIfHoist2] at run
  | succ n ih =>
    cases first <;> simp only [tryIfHoist2] at run
    all_goals repeat' first | contradiction | (split at run)
    all_goals try simp only [destIfEqSome, Option.some.injEq] at *
    all_goals subst_vars
    all_goals try simp only [everyInst, Bool.and_eq_true] at firstValid ⊢
    all_goals repeat' first
      | assumption
      | exact firstValid.1
      | exact firstValid.2
      | exact firstValid.2.1
      | exact firstValid.2.2
      | apply And.intro
      | (apply everyInstConstFp; simp_all [everyInst])
      | (apply ih; assumption)
      | (simp_all only [everyInst, Bool.and_eq_true])

/-- Flapjack-only wrapper exposing the literal successful tryIfHoist1 branch to the original try_if_hoist2_no_inst theorem. No separate HOL theorem has this signature. -/
private theorem tryIfHoist1NoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool)
    (first second out : WordLangProgHOL (BitVec width))
    (run : tryIfHoist1 first second = some out)
    (firstValid : everyInst P first = true) (secondValid : everyInst P second = true) :
    everyInst P out = true := by
  unfold tryIfHoist1 at run
  split at run
  · contradiction
  · exact tryIfHoist2NoInst P _ _ _ _ _ _ () run firstValid rfl secondValid

/-- Duplicate-condition simplification preserves the original predicate through actual successful hoisting and sequence association. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "simp_duplicate_if_no_inst"
  (words_as_type_indexed_bitvec)]
theorem simpDuplicateIfNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) : everyInst P (simpDuplicateIf program) = true := by
  induction program using (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    fun_cases simpDuplicateIf program <;> try simp_all +zetaDelta [everyInst]
    all_goals repeat' first
      | assumption
      | exact source.1
      | exact source.2
      | omega
      | (change sizeOf _ < sizeOf _; simp; omega)
      | apply And.intro
      | apply ih
      | (apply seqAssocNoInst; apply And.intro; rfl)
      | (apply tryIfHoist1NoInst; assumption)
      | split
      | simp_all [everyInst]
    all_goals change sizeOf _ < sizeOf _
    all_goals simp

/-- Flapjack-only projection induction support covering both native exit flags. The original simp_push_out_if_no_inst proof establishes this fact internally, without a separate named declaration. -/
private theorem pushOutIfAuxNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) : everyInst P (pushOutIfAux program).1 = true := by
  induction program using (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction with
  | h program ih =>
    have advance (p out : WordLangProgHOL (BitVec width)) (flag : Bool)
        (run : pushOutIfAux p = (out, flag))
        (smaller : sizeOf p < sizeOf program) (input : everyInst P p = true) :
        everyInst P out = true := by
      simpa only [run] using ih p smaller input
    fun_cases pushOutIfAux program <;> simp_all +zetaDelta [everyInst, -Bool.forall_bool]
    all_goals repeat' first
      | assumption
      | exact source.1
      | exact source.2
      | omega
      | (change sizeOf _ < sizeOf _; simp; omega)
      | apply And.intro
      | apply ih
      | (apply advance; assumption)

/-- Conditional push-out preserves the source predicate for both exit flags and all original constructors. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "simp_push_out_if_no_inst"
  (words_as_type_indexed_bitvec)]
theorem simpPushOutIfNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) : everyInst P (pushOutIf program) = true :=
  pushOutIfAuxNoInst P program source

/-- The complete original compile_exp pipeline preserves an arbitrary instruction predicate, without an output assumption. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "compile_exp_no_inst"
  (words_as_type_indexed_bitvec)]
theorem compileExpNoInst {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (program : WordLangProgHOL (BitVec width))
    (source : everyInst P program = true) : everyInst P (compileExp program) = true := by
  apply simpPushOutIfNoInst
  apply simpDuplicateIfNoInst
  apply everyInstConstFp
  exact seqAssocNoInst P .skip program ⟨rfl, source⟩

end Flapjack.WordConvs.WordSimpInstructions
