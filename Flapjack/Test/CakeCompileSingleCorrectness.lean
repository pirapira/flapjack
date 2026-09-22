import Flapjack.RiscV.CakeCompileSingleCorrectness

/-! Focused regression for the Cake `compile_single_correct` Store slice. -/

namespace Flapjack.Test.CakeCompileSingleCorrectness

open Flapjack Flapjack.RiscV

example (state : State 64) :
    evalWordProgCake state
        (.store (.op .add [.var 2, .const (8 : Word 64)]) 1) =
      some (executeInstructions state
        [.addi 31 2 8, .storeWord 1 31]) := by
  have hcompile :
      wordShareInstToInstructionsCake (width := 64) .store 1
          (.op .add [.var 2, .const (8 : Word 64)]) =
        some [.addi 31 2 8, .storeWord 1 31] := by
    simp [wordShareInstToInstructionsCake, wordExpToInstructionsCake,
      wordExpToInstruction, wordInstToInstruction, registerOfNat]
  exact cakeCompileSingle_store_correct state
    (.op .add [.var 2, .const (8 : Word 64)]) 1 _ hcompile

#check cakeCompileSingle_store_correct

end Flapjack.Test.CakeCompileSingleCorrectness
