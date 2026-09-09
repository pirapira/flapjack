import Flapjack.RiscV.StepCorrectness

/-! Regression coverage for the exact RISC-V instruction-step contracts. -/

namespace Flapjack.RiscV

def stepCountState : State 8 :=
  writeRegister (zeroState 8) 1 7

def stepCountProgram : WordProg (Word 8) :=
  .seq (.assign 2 (.var 1)) (.return 0 [2])

example :
    executeInstructionsCounted stepCountState [.addi 2 1 0] =
      (executeInstructions stepCountState [.addi 2 1 0], 1) := by
  simpa using executeInstructionsCounted_spec stepCountState [.addi 2 1 0]

example :
    wordProgToRiscV (.assign 2 (.var 1) : WordProg (Word 8)) =
      some [.addi 2 1 0] := by
  simp [wordProgToRiscV, wordExpToInstructions, wordExpToInstruction,
    registerOfNat]

example :
    some (executeInstructionsCounted stepCountState [.addi 2 1 0]) =
      (evalWordProg stepCountState
        (.assign 2 (.var 1) : WordProg (Word 8))).map
        (fun final => (final, 1)) := by
  apply wordProgToRiscV_counted_sound_of_straightLine
    stepCountState (.assign 2 (.var 1))
  · exact .assign 2 (.var 1)
  · simp [wordProgToRiscV, wordExpToInstructions, wordExpToInstruction,
      registerOfNat]

example (host : WordFfiHost 8) (state : State 8) :
    executeInstructionsWithFfiCounted host state [] = some (state, 0) := by
  rfl

end Flapjack.RiscV
