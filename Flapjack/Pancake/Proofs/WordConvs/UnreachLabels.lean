import Flapjack.Pancake.Proofs.WordConvs.Unreach

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordUnreach

/-- Flapjack factoring of actual native move-descriptor label preservation.
HOL handles these branches inline; no independently named original. -/
private theorem labelsOfDestSeqMove {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) (n : Nat) (moves : List (Nat × Nat))
    (rest : WordLangProgHOL (BitVec width))
    (found : destSeqMove p = some (n,moves,rest)) : extractLabels rest = extractLabels p := by
  cases p <;> simp_all [destSeqMove, extractLabels]
  case move => rw [← found.2.2]; rfl
  case seq first second => cases first <;> simp_all [extractLabels]

/-- Flapjack stronger list-order factoring of the original SimpSeq label subset
and distinctness proof. The relation is proved from the actual transformation;
no desired output property is assumed. -/
private theorem labelsSublistSimpSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    (extractLabels (simpSeq first second)).Sublist (extractLabels first ++ extractLabels second) := by
  fun_cases simpSeq first second <;> simp_all +zetaDelta [extractLabels]
  all_goals first
    | exact List.sublist_append_left _ _
    | exact List.sublist_append_right _ _
    | exact List.Sublist.refl _
    | (rw [labelsOfDestSeqMove second _ _ _ (by assumption)]; exact List.Sublist.refl _)

/-- Flapjack stronger list-order factoring of HOL's recursive subset and
ALL_DISTINCT proofs. This is derived from literal native Seq_assoc_right. -/
private theorem labelsSublistSeqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    (extractLabels (seqAssocRight first second)).Sublist (extractLabels first ++ extractLabels second) := by
  induction first using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing second with
  | h first ih =>
    fun_cases seqAssocRight first second <;> try simp only [extractLabels]
    case case1 => exact List.Sublist.refl _
    case case2 q1 q2 =>
      have one := ih q1 (by change sizeOf q1 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width)); simp <;> omega)
        (seqAssocRight q2 second)
      have two := ih q2 (by change sizeOf q2 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width)); simp <;> omega) second
      simpa only [List.append_assoc] using one.trans ((List.Sublist.refl _).append two)
    case case3 cmp reg imm q1 q2 =>
      apply (labelsSublistSimpSeq _ _).trans
      simp only [extractLabels]
      apply List.Sublist.append
      · apply List.Sublist.append
        · simpa only [extractLabels, List.append_nil] using
            ih q1 (by change sizeOf q1 < sizeOf (.ite cmp reg imm q1 q2 : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
        · simpa only [extractLabels, List.append_nil] using
            ih q2 (by change sizeOf q2 < sizeOf (.ite cmp reg imm q1 q2 : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
      · exact List.Sublist.refl _
    case case4 q =>
      apply (labelsSublistSimpSeq _ _).trans
      simp only [extractLabels]
      apply List.Sublist.append _ (List.Sublist.refl _)
      simpa only [extractLabels, List.append_nil] using
        ih q (by change sizeOf q < sizeOf (.mustTerminate q : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
    case case5 => exact List.nil_sublist _
    case case6 dest args handler ns cuts q l1 l2 =>
      apply (labelsSublistSimpSeq _ _).trans
      cases handler with
      | none =>
        simp only [extractLabels]
        apply List.Sublist.append _ (List.Sublist.refl _)
        apply List.Sublist.append (List.Sublist.refl _) _
        simpa only [extractLabels, List.append_nil] using
          ih q (by change sizeOf q < sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args none : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
      | some h =>
        rcases h with ⟨n,body,h1,h2⟩
        simp only [extractLabels]
        apply List.Sublist.append _ (List.Sublist.refl _)
        apply List.Sublist.append
        · apply List.Sublist.append (List.Sublist.refl _) _
          simpa only [extractLabels, List.append_nil] using
            ih q (by change sizeOf q < sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args (some (n,body,h1,h2)) : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
        · simpa only [extractLabels, List.append_nil] using
            ih body (by change sizeOf body < sizeOf (.call (some (ns,cuts,q,l1,l2)) dest args (some (n,body,h1,h2)) : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
    case case7 names body exits =>
      apply (labelsSublistSimpSeq _ _).trans
      simp only [extractLabels]
      apply List.Sublist.append _ (List.Sublist.refl _)
      simpa only [extractLabels, List.append_nil] using
        ih body (by change sizeOf body < sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)); simp <;> omega) .skip
    case case8 =>
      simpa only [extractLabels] using labelsSublistSimpSeq first second

/-- Original SimpSeq label-set inclusion for arbitrary programs and labels. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_SimpSeq"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsSimpSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    ∀ label, label ∈ extractLabels (simpSeq first second) →
      label ∈ extractLabels (.seq first second) := by
  intro label member
  exact (labelsSublistSimpSeq first second).subset member

/-- Original recursive right-association label-set inclusion, including all
native accumulator drops and returning handlers. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_Seq_assoc_right_lemma"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsSeqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) :
    ∀ label, label ∈ extractLabels (seqAssocRight first second) →
      label ∈ extractLabels first ∨ label ∈ extractLabels second := by
  intro label member
  exact List.mem_append.mp ((labelsSublistSeqAssocRight first second).subset member)

/-- Original complete remove_unreach label-set inclusion. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_remove_unreach"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsRemoveUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    ∀ label, label ∈ extractLabels (removeUnreach program) → label ∈ extractLabels program := by
  intro label member
  simpa only [extractLabels, List.mem_nil_iff, or_false] using
    extractLabelsSeqAssocRight program .skip label member

/-- Original membership corollary; HOL's set inclusion and membership disjunction
have the same pointwise Lean statement, without an additional premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "MEM_extract_labels_Seq_assoc_right_lemma"
  (words_as_type_indexed_bitvec)]
theorem memExtractLabelsSeqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) (label : Nat × Nat)
    (member : label ∈ extractLabels (seqAssocRight first second)) :
    label ∈ extractLabels first ∨ label ∈ extractLabels second :=
  extractLabelsSeqAssocRight first second label member

/-- Original whole-label-list distinctness implication for native right association. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma"
  (words_as_type_indexed_bitvec)]
theorem distinctExtractLabelsSeqAssocRight {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width))
    (distinct : (extractLabels first ++ extractLabels second).Nodup) :
    (extractLabels (seqAssocRight first second)).Nodup :=
  (labelsSublistSeqAssocRight first second).nodup distinct

/-- Original source-distinctness preservation for native remove_unreach. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ALL_DISTINCT_extract_labels_remove_unreach"
  (words_as_type_indexed_bitvec)]
theorem distinctExtractLabelsRemoveUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (distinct : (extractLabels program).Nodup) :
    (extractLabels (removeUnreach program)).Nodup := by
  apply distinctExtractLabelsSeqAssocRight program .skip
  simpa only [extractLabels, List.append_nil] using distinct

/-- Full original labels_rel_remove_unreach, preserving both label-set inclusion
and source-distinctness implication. No desired output relation is assumed. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_remove_unreach"
  (words_as_type_indexed_bitvec)]
theorem labelsRelRemoveUnreach {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (removeUnreach program)) :=
  ⟨distinctExtractLabelsRemoveUnreach program, extractLabelsRemoveUnreach program⟩

end Flapjack.WordConvs
