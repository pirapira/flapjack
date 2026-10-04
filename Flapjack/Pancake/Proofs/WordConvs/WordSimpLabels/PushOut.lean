import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Sequence

namespace Flapjack.WordConvs
open Flapjack.Compiler.Backend.WordSimp

/-- Full original push-out-if label relation, including branch permutations.
The native auxiliary traversal preserves all label occurrences up to permutation;
no distinct-output or successful-pass premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_push_out_if"
  (words_as_type_indexed_bitvec)]
theorem labelsRelPushOutIf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (pushOutIf program)) := by
  unfold pushOutIf
  fun_induction pushOutIfAux program <;>
    simp_all only [extractLabels, List.nil_append, List.append_nil]
  all_goals first
    | exact labelsRel_refl _
    | solve | apply labelsRel_append <;> first | assumption | exact labelsRel_refl _
    | apply labelsRelAppendImp; apply labelsRel_append <;> assumption

end Flapjack.WordConvs
