import Flapjack.RiscV.CorrectnessStackRiscVAddCarry

/-! Regression coverage for scratch-based StackLang AddCarry lowering. -/

namespace Flapjack.RiscV

open Flapjack

def addCarryStackTestState : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    WordStackRegisterRelationExceptX31 addCarryStackTestState (zeroState 64) := by
  intro register hregister hscratch
  rfl

example :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister addCarryStackTestState 5
          (addCarryWords (addCarryStackTestState.registers 2)
            (addCarryStackTestState.registers 3)
            (addCarryStackTestState.registers 4)).1)
        6
          (addCarryWords (addCarryStackTestState.registers 2)
            (addCarryStackTestState.registers 3)
            (addCarryStackTestState.registers 4)).2)
      (executeInstructions (zeroState 64)
        [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
          .sltu 31 5 31, .or 6 6 31]) := by
  apply wordStackRegisterRelationExceptX31_executeAddCarry
  · intro register hregister hscratch
    rfl
  all_goals try omega
  rfl

end Flapjack.RiscV
