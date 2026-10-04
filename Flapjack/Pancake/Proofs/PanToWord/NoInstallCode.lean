import Flapjack.Pancake.PanToWord
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode

/-!
# `pan_to_wordProof`: no_install/no_alloc/no_mt lemmas

The `(*** no_install/no_alloc/no_mt lemmas ***)` section of
`cakeml/pancake/proofs/pan_to_wordProofScript.sml` (669-700): the code of
`pan_to_word$compile_prog` has no `Install`, `Alloc` or `MustTerminate`, since its
last stage is `loop_to_word$compile`.
-/

namespace Flapjack.PanToWord
open Flapjack Flapjack.WordProps Flapjack.LoopToWord Flapjack.Compiler.Encoders.Asm

/-- HOL `pan_to_word_compile_prog_no_install_code` (`pan_to_wordProofScript.sml:671-677`); HOL's
    free `c prog prog'` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_install_code"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_compile_prog_no_install_code {width : Nat} [NeZero width] (c : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c prog = prog' → noInstallCode (sptFromAList prog') := by
  rintro rfl
  exact loop_compile_no_install_code _

/-- HOL `pan_to_word_compile_prog_no_alloc_code` (`pan_to_wordProofScript.sml:679-685`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_alloc_code"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_compile_prog_no_alloc_code {width : Nat} [NeZero width] (c : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c prog = prog' → noAllocCode (sptFromAList prog') := by
  rintro rfl
  exact loop_compile_no_alloc_code _

/-- HOL `pan_to_word_compile_prog_no_mt_code` (`pan_to_wordProofScript.sml:687-693`). -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_mt_code"
  (words_as_type_indexed_bitvec)]
theorem pan_to_word_compile_prog_no_mt_code {width : Nat} [NeZero width] (c : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    panToWordCompileProgHOL c prog = prog' → noMtCode (sptFromAList prog') := by
  rintro rfl
  exact loop_compile_no_mt_code _

end Flapjack.PanToWord
