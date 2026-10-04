import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Full original compile_word_to_stack_bitmaps (5682-5689), used by
backendProof and pan_to_targetProof: the native top-level compiler with
perf = F returns a nonempty bitmap list headed by 4w, and its output
configuration records the bitmap list length. The proof follows HOL: the
initial bitmap [4w] is a prefix of the output (compile_word_to_stack_isPREFIX)
and the original accounting preserves the zero gap
(compile_word_to_stack_IMP_LENGTH). The only carrier translation is the
positive HOL word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_bitmaps" (words_as_type_indexed_bitvec)]
theorem compileWordToStackBitmaps {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (p : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (c2 : Config)
    (prog1 : List Nat × List (Nat × HolProg width))
    (run : compileNative c false p = (bitmaps, c2, prog1)) :
    (match (generalizing := false) bitmaps with
     | [] => False
     | head :: _ => (4 : BitVec width) = head) ∧
    c2.bitmapsLength = bitmaps.length := by
  simp only [compileNative, Bool.false_eq_true, if_false] at run
  rcases compiled : compileWordToStackNative c false (c.regCount - (5 + c.avoidRegs.length)) p
      (.list [4], 1) with ⟨bodies, frames, output, nextIndex⟩
  rw [compiled] at run
  simp only [Prod.mk.injEq] at run
  obtain ⟨bitmapsEq, configEq, _⟩ := run
  have isPrefix := compileWordToStackIsPrefix c false _ p (.list [4], 1) bodies frames
    (output, nextIndex) compiled
  obtain ⟨left, gap⟩ := compileWordToStackImpLength c false _ p (.list [4]) 1 bodies frames
    output nextIndex ⟨compiled, by simp [appListAppend, appendAux]⟩
  subst bitmapsEq
  subst configEq
  refine ⟨?_, ?_⟩
  · simp only [appListAppend, appendAux, List.singleton_append] at isPrefix
    obtain ⟨rest, restEq⟩ := isPrefix
    simp only [appListAppend]
    rw [← restEq]
    rfl
  · have initial : (appListAppend (AppList.list [(4 : BitVec width)])).length = 1 := by
      simp [appListAppend, appendAux]
    rw [initial] at gap
    show nextIndex = (appListAppend output).length
    omega

end Flapjack.Compiler.Backend.WordToStack.Native
