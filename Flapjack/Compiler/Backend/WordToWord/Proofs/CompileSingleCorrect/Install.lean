import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Leaf
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle
import Flapjack.Misc.Sptree.ToAList
set_option autoImplicit false
namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
namespace CompileSingleCorrectInstallCarrier
/-- Canonical carrier roundtrip infrastructure; no independent HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CompileSingleCorrectInstallCarrier

open Classical in
/-- Full original compile_single_correct Install case (801-822), preserving
all original code/compiler/oracle/domain/gc premises and the existential source
permutation, error branch, complete code relation/domain and post-state result.
Install has no recursive subprogram, so this case needs no induction hypothesis.
The oracle-provided source program list is compiled internally, both buffer
checks and configuration advancement are retained, and original code union is
left-biased. No target-run or post-state premise is added.

The evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8);
this case adds no real arithmetic and makes no full compiler or executed-route
completion claim. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Install {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width)
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.install ptr len dptr dlen names) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, horacle, hgc⟩
  refine ⟨st.permute, ?_⟩
  dsimp only
  rw [show ({st with permute := st.permute} : WordSemStateFiniteExact width C F) = st from rfl]
  rw [evaluate, evaluate]
  simp only [horacle, Function.comp_apply]
  rw [hcomp]
  dsimp only
  simp only [getVar]
  generalize ho : st.compileOracle 0 = entry
  rcases entry with ⟨cfg, progs⟩
  repeat' (split <;> (try simp_all [List.map_cons, holShiftSeq]))
  refine ⟨code_rel_union_fromAList tt kk aa co _ _ _ ⟨hrel, hdom⟩, ?_, ?_, ?_⟩
  · simp [sptDomain_sptUnion, sptDomainFromAList, hdom,
      List.map_map, Function.comp_def, FST_compile_single]
  · simp only [FST_compile_single]
  · rfl
end Flapjack.Compiler.Backend.WordToWord
