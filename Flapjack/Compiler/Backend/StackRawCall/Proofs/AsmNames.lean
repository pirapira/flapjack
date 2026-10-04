import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.RemoveNames

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- HOL `stack_asm_name_comp` (`stack_rawcallProofScript.sml:838-860`): recursive
and top-level raw-call compilation preserve `stack_asm_name` and
`stack_asm_remove`. HOL's boolean equations are Lean `Prop` equalities; the
configuration `c` is free in HOL and implicit here. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_asm_name_comp"
  (words_as_type_indexed_bitvec)]
theorem stackAsmNameComp {width : Nat} [NeZero width] {c : AsmConfigExact width} :
    ∀ (i : Spt Nat) (p : HolProg width),
      (stackAsmName c (comp i p) = stackAsmName c p ∧
        stackAsmName c (compTop i p) = stackAsmName c p) ∧
      (stackAsmRemove c (comp i p) = stackAsmRemove c p ∧
        stackAsmRemove c (compTop i p) = stackAsmRemove c p) := by
  intro info body
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · simp [comp, compTop, h, stackAsmName, stackAsmRemove, ihFirst.1.1, ihSecond.1.1,
        ihFirst.2.1, ihSecond.2.1]
    · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info h
      simp only [comp, compTop, compSeq, destCase]
      split <;> try simp_all [stackAsmName, stackAsmRemove]
      all_goals split <;> try simp_all [stackAsmName, stackAsmRemove]
      all_goals split <;> try simp_all [stackAsmName, stackAsmRemove]
  | _ => simp_all [comp, compTop, stackAsmName, stackAsmRemove]

/-- HOL `stack_alloc_stack_asm_convs` of `stack_rawcallProofScript.sml:862-869`:
raw-call compilation of a whole program preserves `EVERY stack_asm_name` and
`EVERY stack_asm_remove`. HOL's `EVERY (λ(n,p). P p)` is a membership
quantifier over the second component. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_alloc_stack_asm_convs"
  (words_as_type_indexed_bitvec)]
theorem stackAllocStackAsmConvs {width : Nat} [NeZero width] {c : AsmConfigExact width}
    {prog : List (Nat × HolProg width)} :
    (∀ np ∈ compile prog, stackAsmName c np.2) = (∀ np ∈ prog, stackAsmName c np.2) ∧
      (∀ np ∈ compile prog, stackAsmRemove c np.2) = (∀ np ∈ prog, stackAsmRemove c np.2) := by
  simp only [compile, List.forall_mem_map, (stackAsmNameComp _ _).1.2, (stackAsmNameComp _ _).2.2,
    and_self]

end Flapjack.Compiler.Backend.StackRawCall
