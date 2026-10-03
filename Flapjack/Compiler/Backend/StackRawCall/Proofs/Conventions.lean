import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Compiler.Backend.StackProps.CallArgs
import Flapjack.Compiler.Backend.StackProps.AllocArg

/-! `stack_rawcallProofScript.sml:872-941`: raw-call compilation preserves
`reg_bound`, `call_args` and `alloc_arg`, per program and over whole compiled
code, and keeps the procedure names. HOL's equalities of booleans are `↔`. -/

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- HOL `reg_bound_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "reg_bound_comp"
  (words_as_type_indexed_bitvec)]
theorem regBoundComp {width : Nat} [NeZero width] {s : Nat} :
    ∀ (i : Spt Nat) (p : HolProg width),
      (regBound (comp i p) s ↔ regBound p s) ∧ (regBound (compTop i p) s ↔ regBound p s) := by
  intro info body
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, regBound, ihFirst.1, ihSecond.1]
      · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [regBound]
        all_goals split <;> try simp_all [regBound]
        all_goals split <;> try simp_all [regBound]
    · simp [compTop, regBound, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, regBound]

/-- HOL `call_args_comp`. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "call_args_comp"
  (words_as_type_indexed_bitvec)]
theorem callArgsComp {width : Nat} [NeZero width] {r1 r2 r3 r4 r5 : Nat} :
    ∀ (i : Spt Nat) (p : HolProg width),
      (callArgs (comp i p) r1 r2 r3 r4 r5 ↔ callArgs p r1 r2 r3 r4 r5) ∧
      (callArgs (compTop i p) r1 r2 r3 r4 r5 ↔ callArgs p r1 r2 r3 r4 r5) := by
  intro info body
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, callArgs, ihFirst.1, ihSecond.1]
      · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [callArgs]
        all_goals split <;> try simp_all [callArgs]
        all_goals split <;> try simp_all [callArgs]
    · simp [compTop, callArgs, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, callArgs]

/-- HOL `call_arg_comp` (on `alloc_arg`). -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "call_arg_comp"
  (words_as_type_indexed_bitvec)]
theorem callArgComp {width : Nat} [NeZero width] :
    ∀ (i : Spt Nat) (p : HolProg width),
      (allocArg (comp i p) ↔ allocArg p) ∧ (allocArg (compTop i p) ↔ allocArg p) := by
  intro info body
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, allocArg, ihFirst.1, ihSecond.1]
      · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [allocArg]
        all_goals split <;> try simp_all [allocArg]
        all_goals split <;> try simp_all [allocArg]
    · simp [compTop, allocArg, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, allocArg]

/-- HOL `stack_rawcall_reg_bound`. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_rawcall_reg_bound"
  (words_as_type_indexed_bitvec)]
theorem stackRawcallRegBound {width : Nat} [NeZero width] {sp : Nat}
    {prog1 : List (Nat × HolProg width)} :
    (∀ p ∈ (compile prog1).map Prod.snd, regBound p sp) ↔
      (∀ p ∈ prog1.map Prod.snd, regBound p sp) := by
  simp only [compile, List.map_map, Function.comp_def, List.mem_map, Prod.exists]
  constructor
  · rintro h p ⟨x, q, hx, rfl⟩
    exact (regBoundComp (collectInfo prog1 .ln) q).2.mp (h _ ⟨x, q, hx, rfl⟩)
  · rintro h p ⟨x, q, hx, rfl⟩
    exact (regBoundComp (collectInfo prog1 .ln) q).2.mpr (h q ⟨x, q, hx, rfl⟩)

/-- HOL `stack_alloc_call_args` (of `stack_rawcallProof`). -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_alloc_call_args"
  (words_as_type_indexed_bitvec)]
theorem stackRawcallCallArgs {width : Nat} [NeZero width]
    {prog1 : List (Nat × HolProg width)} :
    (∀ p ∈ (compile prog1).map Prod.snd, callArgs p 1 2 3 4 0) ↔
      (∀ p ∈ prog1.map Prod.snd, callArgs p 1 2 3 4 0) := by
  simp only [compile, List.map_map, Function.comp_def, List.mem_map, Prod.exists]
  constructor
  · rintro h p ⟨x, q, hx, rfl⟩
    exact (callArgsComp (collectInfo prog1 .ln) q).2.mp (h _ ⟨x, q, hx, rfl⟩)
  · rintro h p ⟨x, q, hx, rfl⟩
    exact (callArgsComp (collectInfo prog1 .ln) q).2.mpr (h q ⟨x, q, hx, rfl⟩)

/-- HOL `MAP_FST_compile` (of `stack_rawcallProof`). -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "MAP_FST_compile"
  (words_as_type_indexed_bitvec)]
theorem mapFstCompile {width : Nat} [NeZero width] {code : List (Nat × HolProg width)} :
    (compile code).map Prod.fst = code.map Prod.fst := by
  simp [compile, Function.comp_def]

end Flapjack.Compiler.Backend.StackRawCall
