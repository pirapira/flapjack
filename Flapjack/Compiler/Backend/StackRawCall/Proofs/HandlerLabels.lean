import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackProps.CodeLabels

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- HOL `stack_get_handler_labels_comp` (`stack_rawcallProofScript.sml:956-975`):
recursive and top-level raw-call compilation preserve the handler labels of
every owner. There is no premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml"
  "stack_get_handler_labels_comp" (words_as_type_indexed_bitvec)]
theorem stackGetHandlerLabelsComp {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (p : HolProg width) (k : Nat),
      stackGetHandlerLabels k (comp i p) = stackGetHandlerLabels k p ∧
      stackGetHandlerLabels k (compTop i p) = stackGetHandlerLabels k p := by
  intro info body k
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, stackGetHandlerLabels, ihFirst.1, ihSecond.1]
      · obtain ⟨k', dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [stackGetHandlerLabels]
        all_goals split <;> try simp_all [stackGetHandlerLabels]
        all_goals split <;> try simp_all [stackGetHandlerLabels]
    · simp [compTop, stackGetHandlerLabels, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, stackGetHandlerLabels]

end Flapjack.Compiler.Backend.StackRawCall
