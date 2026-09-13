import Flapjack.RiscV.InstructionRelabel

/-! Executable checks for the CakeML register-field mapping. -/

namespace Flapjack.Test.InstructionTransfer

open Flapjack Flapjack.RiscV

#guard
  (match relabelInstruction ((.add (0 : Fin 32) 1 27) : Instruction 64) with
   | .add destination sourceLeft sourceRight =>
       destination.val == 1 && sourceLeft.val == 10 && sourceRight.val == 0
   | _ => false)

#guard
  (match relabelInstruction ((.branchEq (1 : Fin 32) 4 8) : Instruction 64) with
   | .branchEq sourceLeft sourceRight offset =>
       sourceLeft.val == 10 && sourceRight.val == 13 && offset.toNat == 8
   | _ => false)

#guard
  (match relabelInstruction (.ecall : Instruction 64) with
   | .ecall => true
   | _ => false)

end Flapjack.Test.InstructionTransfer
