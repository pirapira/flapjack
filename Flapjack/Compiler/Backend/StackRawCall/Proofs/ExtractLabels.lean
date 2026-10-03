import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackProps.OrderedLabels

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackPropsCodeLabels

/-- HOL `extract_labels_comp` (`stack_rawcallProofScript.sml:818-832`):
recursive and top-level raw-call compilation preserve the ordered extracted
labels. There is no premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "extract_labels_comp"
  (words_as_type_indexed_bitvec)]
theorem extractLabelsComp {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (p : HolProg width),
      extractLabels (comp i p) = extractLabels p ∧
      extractLabels (compTop i p) = extractLabels p := by
  intro info body
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, extractLabels, ihFirst.1, ihSecond.1]
      · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [extractLabels]
        all_goals split <;> try simp_all [extractLabels]
        all_goals split <;> try simp_all [extractLabels]
    · simp [compTop, extractLabels, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, extractLabels]

end Flapjack.Compiler.Backend.StackRawCall
