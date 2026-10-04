import Flapjack.Compiler.Backend.WordToWord.Proofs.Syntactic
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.CompileExp
import Flapjack.Pancake.Proofs.WordConvs.InstSelectProgram
import Flapjack.Pancake.Proofs.WordConvs.SSALabelFull
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead
import Flapjack.Pancake.Proofs.WordConvs.WordCse
import Flapjack.Pancake.Proofs.WordConvs.CopyProp
import Flapjack.Pancake.Proofs.WordConvs.ThreeToTwo
import Flapjack.Pancake.Proofs.WordConvs.UnreachLabels
import Flapjack.Pancake.Proofs.WordConvs.WordAlloc
import Flapjack.Pancake.Proofs.WordConvs.RemoveMustTerminate

/-! First two original conjunction sections; remaining five conventions stay open. -/
namespace Flapjack.Compiler.Backend.WordToWord.CompileConventions
open Flapjack Flapjack.WordConvs Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord

/-- Flapjack infrastructure: sixth original dead-code law, used inline in HOL. -/
private theorem deadLabels {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) :
    extractLabels p = extractLabels (WordAlloc.removeDeadProg p) :=
  (removeDeadProgConventions (fun _ => true) p c).2.2.2.2.2

/-- Flapjack infrastructure: fifth original termination law, used inline in HOL. -/
private theorem terminationLabels {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (k : Nat) (p : WordLangProgHOL (BitVec width)) :
    extractLabels p = extractLabels (WordRemove.removeMustTerminate p) :=
  (removeMustTerminateConventions (fun _ => true) p c k).2.2.2.2

/-- Flapjack infrastructure: actual eleven-pass label chain, proved inline in HOL;
no desired output relation is assumed. -/
private theorem singleLabels {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (entry : (Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)) :
    labelsRel (extractLabels entry.1.2.2)
      (extractLabels (fullCompileSingle two k alg c entry).2.2) := by
  rcases entry with ⟨⟨name, args, program⟩, col⟩
  simp only [fullCompileSingle, compileSingle]
  rw [← terminationLabels c k, ← wordAlloc_labPres, ← deadLabels c]
  apply labelsRel_trans (WordSimpLabels.extractLabelsCompileExp program)
  have h := labelsRelRemoveUnreach
    (WordInst.threeToTwoRegProg two
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim
        (WordAlloc.removeDeadProg (WordAlloc.fullSsaCcTrans args
          (WordInst.instSelect c (maxVarHOL (WordSimp.compileExp program) + 1)
            (WordSimp.compileExp program)))))))
  simpa only [← threeToTwoRegProg_labPres, extract_labels_copy_prop,
    extract_labels_word_common_subexp_elim, ← deadLabels c,
    ← WordAlloc.fullSsaCcTrans_labPres, ← instSelect_labPres] using h

/-- Flapjack infrastructure: equal-length actual oracle zip induction; HOL uses EL/ZIP. -/
private theorem zipSections {width : Nat} [NeZero width] (two : Bool)
    (k alg : Nat) (c : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (oracles : List (Option (Spt Nat))) (lengths : oracles.length = programs.length) :
    ((programs.zip oracles).map (fullCompileSingle two k alg c)).map Prod.fst =
        programs.map Prod.fst ∧
    List.Forall₂ labelsRel (programs.map (fun p => extractLabels p.2.2))
      (((programs.zip oracles).map (fullCompileSingle two k alg c)).map
        (fun p => extractLabels p.2.2)) := by
  induction programs generalizing oracles with
  | nil => cases oracles <;> simp_all
  | cons p ps ih =>
    cases oracles with
    | nil => simp at lengths
    | cons oracle rest =>
      have tailLength : rest.length = ps.length := by simpa using lengths
      obtain ⟨names, labels⟩ := ih rest tailLength
      constructor
      · simpa [fullCompileSingle, compileSingle] using congrArg (List.cons p.1) names
      · simpa only [List.zip_cons_cons, List.map_cons] using
          List.Forall₂.cons (singleLabels two k alg c (p, oracle)) labels

/-- Original958–1014 first two conjunction sections: whole names and EVERY2 labels.
Retains original no-share-or-ISA input guard, unused in these structural sections.
The remaining five output conventions are a separate unfinished assembly. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml"
  "compile_to_word_conventions" (words_as_type_indexed_bitvec)]
theorem compileNamesLabels {width : Nat} [NeZero width] (wc : Config)
    (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (_guard : ∀ p ∈ programs, noShareInstSubprogsHOL p.2.2 = true ∨ ac.isa ≠ .ag32) :
    (compile wc ac programs).2.map Prod.fst = programs.map Prod.fst ∧
    List.Forall₂ labelsRel (programs.map (fun p => extractLabels p.2.2))
      ((compile wc ac programs).2.map (fun p => extractLabels p.2.2)) := by
  exact zipSections ac.twoRegArith (ac.regCount - (5 + ac.avoidRegs.length))
    wc.regAlg ac programs (nextNOracle programs.length wc.colOracle).1
    (compile_zip_length wc programs)

end Flapjack.Compiler.Backend.WordToWord.CompileConventions
