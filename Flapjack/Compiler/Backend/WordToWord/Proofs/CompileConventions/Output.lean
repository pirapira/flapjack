import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Labels
import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull
import Flapjack.Pancake.Proofs.WordConvs.Unreach
import Flapjack.Pancake.Proofs.WordConvs.UnreachPreAlloc
import Flapjack.Pancake.Proofs.WordConvs.WordSimpInstructions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Full
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.FullInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.AllocationConventions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.InstructionConventions
import Flapjack.Compiler.Backend.WordCse.Proofs.Conventions

/-! The five original output conditions and whole compile-to-word conventions. -/
namespace Flapjack.Compiler.Backend.WordToWord.CompileConventions
open Flapjack Flapjack.WordConvs Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordInst

/-- Flapjack infrastructure: original inline unconditional flat-output proof. -/
private theorem singleFlat {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (entry : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    flatExpConventions (fullCompileSingle two k alg c entry).2.2 = true := by
  rcases entry with ⟨⟨name, args, program⟩, col⟩
  simp only [fullCompileSingle, compileSingle]
  apply (removeMustTerminateConventions (fun _ => true) _ c k).1
  apply wordAlloc_flatExpConventions
  apply (removeDeadProgConventions (fun _ => true) _ c).1
  apply flatExpConventions_removeUnreach
  apply threeToTwoRegProg_flatExpConventions
  apply flat_exp_conventions_copy_prop
  apply flat_exp_conventions_word_common_subexp_elim
  apply (removeDeadProgConventions (fun _ => true) _ c).1
  apply WordAlloc.fullSsaCcTrans_flatExpConventions
  exact instSelect_flatExpConventions _ _ _

/-- Flapjack infrastructure: original inline unconditional post-allocation proof. -/
private theorem singlePost {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (entry : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    postAllocConventionsHOL k (fullCompileSingle two k alg c entry).2.2 = true := by
  rcases entry with ⟨⟨name, args, program⟩, col⟩
  simp only [fullCompileSingle, compileSingle]
  apply (removeMustTerminateConventions (fun _ => true) _ c k).2.2.1
  apply WordAlloc.prePostConventions_wordAlloc
  apply (removeDeadProgConventions (fun _ => true) _ c).2.2.1
  apply preAllocConventions_removeUnreach
  apply threeToTwoRegProg_preAllocConventions
  apply pre_alloc_conventions_copy_prop
  apply WordCse.pre_alloc_conventions_word_common_subexp_elim
  apply (removeDeadProgConventions (fun _ => true) _ c).2.2.1
  exact WordAlloc.fullSsaCcTrans_preAllocConventions _ _

/-- Flapjack infrastructure: original inline instruction-validity chain with
only the original source instruction and zero-offset premises. -/
private theorem singleValid {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (entry : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat))
    (addressZero : addrOffsetOk c 0 = true) (halfZero : hwOffsetOk c 0 = true)
    (byteZero : byteOffsetOk c 0 = true)
    (source : everyInst (fun i => instOkLessExact c (HolInst.ofWordLangInst i))
      entry.1.2.2 = true) :
    fullInstOkLessExact c (fullCompileSingle two k alg c entry).2.2 = true := by
  rcases entry with ⟨⟨name, args, program⟩, col⟩
  simp only [fullCompileSingle, compileSingle]
  apply (removeMustTerminateConventions (fun _ => true) _ c k).2.1
  apply WordAlloc.wordAlloc_fullInstOkLess
  apply (removeDeadProgConventions (fun _ => true) _ c).2.1
  apply fullInstOkLess_removeUnreach
  apply threeToTwoRegProg_fullInstOkLess
  apply full_inst_ok_less_copy_prop
  apply WordCse.full_inst_ok_less_word_common_subexp_elim
  apply (removeDeadProgConventions (fun _ => true) _ c).2.1
  apply WordAlloc.fullSsaCcTrans_fullInstOkLess
  apply instSelect_fullInstOkLess _ _ _ addressZero halfZero byteZero
  exact WordSimpInstructions.compileExpNoInst _ _ source

/-- Flapjack infrastructure: original inline enabled two-register proof. -/
private theorem singleTwo {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (entry : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat))
    (enabled : two = true) :
    everyInst twoRegInst (fullCompileSingle two k alg c entry).2.2 = true := by
  rcases entry with ⟨⟨name, args, program⟩, col⟩
  simp only [fullCompileSingle, compileSingle]
  apply (removeMustTerminateConventions twoRegInst _ c k).2.2.2.1
  apply wordAlloc_twoRegInst
  apply (removeDeadProgConventions twoRegInst _ c).2.2.2.1
  apply everyInst_removeUnreach
  exact threeToTwoRegProg_twoRegInst _ _ enabled

/-- Original1014–1065 full EVERY output-convention section: all five conditions,
including global input instruction and three zero-offset guards, retained.
No target conventions, pass success or evaluation are assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "compile_to_word_conventions" (words_as_type_indexed_bitvec)]
theorem compileOutputConventions {width : Nat} [NeZero width] (wc : Config)
    (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guard : ∀ p ∈ programs, noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32) :
    ∀ p ∈ (compile wc ac programs).2,
      flatExpConventions p.2.2 = true ∧
      postAllocConventionsHOL (ac.regCount - (5 + ac.avoidRegs.length)) p.2.2 = true ∧
      ((∀ q ∈ programs, everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i)) q.2.2 = true) ∧
        addrOffsetOk ac 0 = true ∧ hwOffsetOk ac 0 = true ∧ byteOffsetOk ac 0 = true →
        fullInstOkLessExact ac p.2.2 = true) ∧
      (ac.twoRegArith = true → everyInst twoRegInst p.2.2 = true) ∧
      (noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32) := by
  intro p member
  change p ∈ ((programs.zip (nextNOracle programs.length wc.colOracle).1).map
    (fullCompileSingle ac.twoRegArith (ac.regCount - (5 + ac.avoidRegs.length)) wc.regAlg ac)) at member
  obtain ⟨entry, inZip, rfl⟩ := List.mem_map.mp member
  have inputMember := (List.of_mem_zip inZip).1
  refine ⟨singleFlat _ _ _ _ entry, singlePost _ _ _ _ entry, ?_, ?_, ?_⟩
  · intro valid
    exact singleValid _ _ _ _ entry valid.2.1 valid.2.2.1 valid.2.2.2
      (valid.1 entry.1 inputMember)
  · exact singleTwo _ _ _ _ entry
  · rcases guard entry.1 inputMember with source | otherIsa
    · exact Or.inl (full_compile_single_no_share_inst entry _ _ _ _ source)
    · exact Or.inr otherIsa

/-- Whole original958–1065 theorem, all original conjuncts. Original
input guard and conditional output guards retained. Actual native compiler
pipeline determines every result; no target-run or output relation premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "compile_to_word_conventions" (words_as_type_indexed_bitvec)]
theorem compileToWordConventions {width : Nat} [NeZero width] (wc : Config)
    (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guard : ∀ p ∈ programs, noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32) :
    (compile wc ac programs).2.map Prod.fst = programs.map Prod.fst ∧
    List.Forall₂ labelsRel (programs.map (fun p => extractLabels p.2.2))
      ((compile wc ac programs).2.map (fun p => extractLabels p.2.2)) ∧
    (∀ p ∈ (compile wc ac programs).2,
      flatExpConventions p.2.2 = true ∧
      postAllocConventionsHOL (ac.regCount - (5 + ac.avoidRegs.length)) p.2.2 = true ∧
      ((∀ q ∈ programs, everyInst (fun i => instOkLessExact ac (HolInst.ofWordLangInst i)) q.2.2 = true) ∧
        addrOffsetOk ac 0 = true ∧ hwOffsetOk ac 0 = true ∧ byteOffsetOk ac 0 = true →
        fullInstOkLessExact ac p.2.2 = true) ∧
      (ac.twoRegArith = true → everyInst twoRegInst p.2.2 = true) ∧
      (noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32)) := by
  obtain ⟨names, labels⟩ := compileNamesLabels wc ac programs guard
  exact ⟨names, labels, compileOutputConventions wc ac programs guard⟩

end Flapjack.Compiler.Backend.WordToWord.CompileConventions
