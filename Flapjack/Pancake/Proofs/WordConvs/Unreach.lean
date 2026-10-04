import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.WfCutsets

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordUnreach Flapjack.Compiler.Encoders.Asm

/-- Flapjack factoring of HOL's constructor analysis inside every_inst_SimpSeq.
HOL has no separately named declaration for this descriptor implication. -/
private theorem everyInst_ofDestSeqMove {width : Nat} [NeZero width]
    (predicate : WordLangInst (BitVec width) → Bool)
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : everyInst predicate program = true) :
    everyInst predicate rest = true := by
  cases program <;> simp_all [destSeqMove, everyInst]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [everyInst]

/-- Original generic instruction-predicate preservation for literal SimpSeq,
with the original two source-programme premises. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "every_inst_SimpSeq" (words_as_type_indexed_bitvec)]
theorem everyInst_simpSeq {width : Nat} [NeZero width]
    (predicate : WordLangInst (BitVec width) → Bool)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : everyInst predicate first = true)
    (secondValid : everyInst predicate second = true) :
    everyInst predicate (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [everyInst]
  all_goals
    first
    | apply everyInst_ofDestSeqMove predicate second <;> assumption
    | simp_all +zetaDelta [everyInst]

/-- Flapjack factoring of the same native descriptor analysis for the original
flat-convention proof; HOL has no separately named descriptor theorem. -/
private theorem flatExpConventions_ofDestSeqMove {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : flatExpConventions program = true) :
    flatExpConventions rest = true := by
  cases program <;> simp_all [destSeqMove, flatExpConventions]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [flatExpConventions]

/-- Original flat-expression preservation for literal SimpSeq, retaining both
original source flat-convention premises and every move-merging branch. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_SimpSeq" (words_as_type_indexed_bitvec)]
theorem flatExpConventions_simpSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : flatExpConventions first = true)
    (secondValid : flatExpConventions second = true) :
    flatExpConventions (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [flatExpConventions]
  all_goals
    first
    | apply flatExpConventions_ofDestSeqMove second <;> assumption
    | simp_all +zetaDelta [flatExpConventions]

/-- Original generic instruction-predicate preservation for right association,
with both source-programme premises, including all returning call handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "every_inst_Seq_assoc_right_lemma" (words_as_type_indexed_bitvec)]
theorem everyInst_seqAssocRight {width : Nat} [NeZero width]
    (predicate : WordLangInst (BitVec width) → Bool)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : everyInst predicate first = true)
    (secondValid : everyInst predicate second = true) :
    everyInst predicate (seqAssocRight first second) = true := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [everyInst, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply everyInst_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [everyInst, Bool.and_eq_true]
        | split
        | constructor

/-- Original flat-expression convention preservation for right association,
with both source-programme premises, including all returning call handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_Seq_assoc_right_lemma" (words_as_type_indexed_bitvec)]
theorem flatExpConventions_seqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : flatExpConventions first = true)
    (secondValid : flatExpConventions second = true) :
    flatExpConventions (seqAssocRight first second) = true := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [flatExpConventions, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply flatExpConventions_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [flatExpConventions, Bool.and_eq_true]
        | split
        | constructor

/-- Original source instruction-predicate preservation for remove_unreach. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "every_inst_remove_unreach" (words_as_type_indexed_bitvec)]
theorem everyInst_removeUnreach {width : Nat} [NeZero width]
    (predicate : WordLangInst (BitVec width) → Bool)
    (program : WordLangProgHOL (BitVec width))
    (source : everyInst predicate program = true) :
    everyInst predicate (removeUnreach program) = true :=
  everyInst_seqAssocRight predicate program .skip source rfl

/-- Original source flat-convention preservation for remove_unreach. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_remove_unreach" (words_as_type_indexed_bitvec)]
theorem flatExpConventions_removeUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (source : flatExpConventions program = true) :
    flatExpConventions (removeUnreach program) = true :=
  flatExpConventions_seqAssocRight program .skip source rfl

/-- Flapjack factoring of the descriptor analysis for the `wf_cutsets` proof;
HOL has no separately named descriptor theorem. -/
private theorem wfCutsets_ofDestSeqMove {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : wfCutsets program) :
    wfCutsets rest := by
  cases program <;> simp_all [destSeqMove, wfCutsets]
  case move =>
    rw [← descriptor.2.2]
    simp [wfCutsets]
  case seq first second =>
    cases first <;> simp_all [wfCutsets]

/-- HOL `wf_cutsets_SimpSeq` (`wordConvsProofScript.sml:2668-2679`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "wf_cutsets_SimpSeq" (words_as_type_indexed_bitvec)]
theorem wfCutsets_simpSeq {width : Nat} [NeZero width]
    (p1 p2 : WordLangProgHOL (BitVec width)) (h : wfCutsets p1 ∧ wfCutsets p2) :
    wfCutsets (simpSeq p1 p2) := by
  obtain ⟨firstValid, secondValid⟩ := h
  fun_cases simpSeq p1 p2 <;> simp_all +zetaDelta [wfCutsets]
  all_goals
    first
    | apply wfCutsets_ofDestSeqMove p2 <;> assumption
    | simp_all +zetaDelta [wfCutsets]

/-- HOL `wf_cutsets_Seq_assoc_right_lemma` (`wordConvsProofScript.sml:2681-2695`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "wf_cutsets_Seq_assoc_right_lemma" (words_as_type_indexed_bitvec)]
theorem wfCutsets_seqAssocRight {width : Nat} [NeZero width] :
    ∀ (p1 p2 : WordLangProgHOL (BitVec width)),
      wfCutsets p1 ∧ wfCutsets p2 → wfCutsets (seqAssocRight p1 p2) := by
  intro first second ⟨firstValid, secondValid⟩
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [wfCutsets]
    all_goals
      repeat' first
        | (apply wfCutsets_simpSeq; constructor)
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [wfCutsets]
        | split
        | constructor

/-- HOL `wf_cutsets_remove_unreach` (`wordConvsProofScript.sml:2697-2703`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "wf_cutsets_remove_unreach" (words_as_type_indexed_bitvec)]
theorem wfCutsets_removeUnreach {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    wfCutsets p → wfCutsets (removeUnreach p) :=
  fun h => wfCutsets_seqAssocRight p .skip ⟨h, trivial⟩

/-- Flapjack factoring of the same native descriptor analysis for the original
full-instruction proof; HOL has no separately named descriptor theorem. -/
private theorem fullInstPolicy_ofDestSeqMove {width : Nat} [NeZero width]
    (instPolicy : WordLangInst (BitVec width) → Bool)
    (addrPolicy : HolMemop → BitVec width → Bool)
    (program : WordLangProgHOL (BitVec width)) (priority : Nat)
    (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (descriptor : destSeqMove program = some (priority, moves, rest))
    (source : fullInstOkLessWith instPolicy addrPolicy program = true) :
    fullInstOkLessWith instPolicy addrPolicy rest = true := by
  cases program <;> simp_all [destSeqMove, fullInstOkLessWith]
  case move =>
    rw [← descriptor.2.2]
    rfl
  case seq first second =>
    cases first <;> simp_all [fullInstOkLessWith]

/-- Flapjack-only policy factoring of full instruction preservation for literal SimpSeq, retaining both
source policy premises and every move-merging branch. HOL has no separately
named policy theorem. -/
private theorem fullInstPolicy_simpSeq {width : Nat} [NeZero width]
    (instPolicy : WordLangInst (BitVec width) → Bool)
    (addrPolicy : HolMemop → BitVec width → Bool)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : fullInstOkLessWith instPolicy addrPolicy first = true)
    (secondValid : fullInstOkLessWith instPolicy addrPolicy second = true) :
    fullInstOkLessWith instPolicy addrPolicy (simpSeq first second) = true := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [fullInstOkLessWith]
  all_goals
    first
    | apply fullInstPolicy_ofDestSeqMove instPolicy addrPolicy second <;> assumption
    | simp_all +zetaDelta [fullInstOkLessWith]

/-- Original full instruction-validity preservation for right association,
with both source-programme premises, including all returning call handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "full_inst_ok_less_Seq_assoc_right_lemma" (words_as_type_indexed_bitvec)]
theorem fullInstOkLess_seqAssocRight {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (first second : WordLangProgHOL (BitVec width))
    (firstValid : fullInstOkLessExact config first = true)
    (secondValid : fullInstOkLessExact config second = true) :
    fullInstOkLessExact config (seqAssocRight first second) = true := by
  simp only [fullInstOkLessExact] at firstValid secondValid ⊢
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp_all +zetaDelta only [fullInstOkLessWith, Bool.and_eq_true]
    all_goals
      repeat' first
        | apply fullInstPolicy_simpSeq
        | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
        | assumption
        | simp_all +zetaDelta only [fullInstOkLessWith, Bool.and_eq_true]
        | split
        | constructor

/-- Original full instruction-validity preservation for remove_unreach. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "full_inst_ok_less_remove_unreach" (words_as_type_indexed_bitvec)]
theorem fullInstOkLess_removeUnreach {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : fullInstOkLessExact config program = true) :
    fullInstOkLessExact config (removeUnreach program) = true :=
  fullInstOkLess_seqAssocRight config program .skip source rfl

end Flapjack.WordConvs
