import Flapjack.RiscV.CakeSoundness

/-!
Lean counterpart of the `Store` branch of Cake's
`compile_single_correct` (`cakeml/compiler/backend/proofs/word_to_wordProofScript.sml`).

The original proof relates the source `Store` evaluator to the code emitted by
the Cake word-to-word compiler.  This slice keeps the same proof-relevant
shape at Flapjack's checked RISC-V boundary: the source address expression,
stored word, emitted instruction list, and machine state all remain explicit.
It deliberately uses the Cake-faithful list-valued selector, so address
materialization is not replaced by the historical one-instruction shortcut.
-/

namespace Flapjack.RiscV

/-- Cake-faithful `compile_single_correct` Store case for the supported
straight-line RISC-V fragment. -/
theorem cakeCompileSingle_store_correct [NeZero width]
    (state : State width) (address : WordExp (Word width)) (value : Nat)
    (code : List (Instruction width))
    (hcompile : wordShareInstToInstructionsCake (width := width) .store value address =
      some code) :
    evalWordProgCake state (.store address value) =
      some (executeInstructions state code) := by
  exact wordProgToRiscVCake_sound_of_straightLine state
    (.store address value) (.store address value) code
    (by simpa [wordProgToRiscVCake] using hcompile)

end Flapjack.RiscV
