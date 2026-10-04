import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Hoist
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.PushOut

namespace Flapjack.WordConvs.WordSimpLabels
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Full original compile_exp label relation for every native program. Every
stage is the actual reviewed compiler operation; label containment and the
source-distinctness implication are derived without an output property premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_compile_exp"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsCompileExp {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (compileExp program)) := by
  unfold compileExp
  have reassoc : labelsRel (extractLabels program) (extractLabels (seqAssoc .skip program)) := by
    rw [extractLabelsSeqAssoc]
    exact labelsRel_refl _
  exact labelsRel_trans reassoc
    (labelsRel_trans (extractLabelsConstFp (seqAssoc .skip program))
      (labelsRel_trans (labelsRelSimpDuplicateIf (constFp (seqAssoc .skip program)))
        (labelsRelPushOutIf (simpDuplicateIf (constFp (seqAssoc .skip program))))))

end Flapjack.WordConvs.WordSimpLabels
