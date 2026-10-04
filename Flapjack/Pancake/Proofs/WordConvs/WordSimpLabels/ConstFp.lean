import Flapjack.HolRef
-- Reuse the accepted native matcher providers.
import Flapjack.Pancake.Proofs.WordConvs.NotCreatedPasses
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.Sequence
import Mathlib.Tactic

/-!
Label preservation of the exact native constant-folding loop and its wrapper.
The loop may discard an unselected conditional branch, so its labels need not
be equal to the input's. The actual output labels form a sublist of the original
labels, establishing both source containment and the original distinctness
implication. Native Spt knowledge and every input/output component remain
arbitrary. This is the constant-folding prerequisite of the full compile_exp
label theorem; hoisting, push-out and the complete compiler remain separate.
-/

namespace Flapjack.WordConvs.WordSimpLabels
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Flapjack-only list reasoning used to derive both clauses of labelsRel.
There is no separate HOL declaration with this stronger sublist premise. -/
private theorem labelsRelOfSublist {β : Type} {oldLabels newLabels : List β}
    (ordered : newLabels.Sublist oldLabels) : labelsRel oldLabels newLabels :=
  ⟨fun distinct => distinct.sublist ordered, fun _ member => ordered.subset member⟩

/-- Flapjack-only stronger induction invariant for the actual loop projection.
The HOL proof handles branch containment and distinctness directly; this
ordered-sublist statement is internal support, not a named HOL port. -/
private theorem constFpLoopLabelsSublist {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)) :
    (extractLabels (constFpLoop program cs).1).Sublist (extractLabels program) := by
  fun_induction constFpLoop program cs <;>
    simp_all [extractLabels, extractLabelsDropConsts]
  all_goals apply List.Sublist.append <;> assumption

/-- Full original loop theorem: an actual returned program/map pair preserves
both clauses of labelsRel, without an output invariant hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_const_fp_loop"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsConstFpLoop {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
    (out : WordLangProgHOL (BitVec width)) (outState : Spt (BitVec width))
    (run : constFpLoop program cs = (out, outState)) :
    labelsRel (extractLabels program) (extractLabels out) := by
  apply labelsRelOfSublist
  simpa only [run] using constFpLoopLabelsSublist program cs

/-- Full original constant-folding wrapper theorem for every native program. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_const_fp"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsConstFp {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (constFp program)) :=
  labelsRelOfSublist (constFpLoopLabelsSublist program .ln)

end Flapjack.WordConvs.WordSimpLabels
