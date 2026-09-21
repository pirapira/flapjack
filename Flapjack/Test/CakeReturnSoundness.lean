import Flapjack.RiscV.CakeSoundness

/-! Focused Cake function-selector soundness for the return-carrier boundary.
    This is separate from the constants API: a return emits no instructions and
    reads the validated register list from the incoming state. -/

namespace Flapjack.Test.CakeReturnSoundness

open Flapjack
open Flapjack.RiscV

def returnSelectorGuard : Bool :=
  match wordFunctionToRiscVCake
      (.return 0 [4] : WordProg (Word 64)) with
  | some ([], [4]) => true
  | _ => false

#guard returnSelectorGuard

example (state : State 64) :
    evalWordFunctionCake state (.return 0 [4] : WordProg (Word 64)) =
      some (state, [readRegister state 4]) := by
  have hcompile : wordFunctionToRiscVCake
      (.return 0 [4] : WordProg (Word 64)) =
      some (([] : List (Instruction 64)), ([4] : List (Fin 32))) := by
    simp [wordFunctionToRiscVCake, registerOfNat]
  have h := wordFunctionToRiscVCake_return_sound state 0 [4] [] [4] hcompile
  simpa [executeInstructions, registerOfNat] using h

def runChecks : IO Bool := do
  if returnSelectorGuard then
    IO.println "PASS Cake function return-carrier selector and soundness"
  else
    IO.println "FAIL Cake function return-carrier selector and soundness"
  pure returnSelectorGuard

end Flapjack.Test.CakeReturnSoundness
