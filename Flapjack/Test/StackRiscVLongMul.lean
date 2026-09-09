import Flapjack.RiscV.CorrectnessStackRiscVLongMul

/-! Regression coverage for StackLang long multiplication lowering. -/

namespace Flapjack.RiscV

open Flapjack

def longMulStackTestState : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    WordStackRegisterRelation longMulStackTestState (zeroState 64) := by
  intro register hregister
  rfl

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister longMulStackTestState 5
          (BitVec.ofNat 64
            ((longMulStackTestState.registers 2).toNat *
              (longMulStackTestState.registers 3).toNat / 2 ^ 64)))
        6 (longMulStackTestState.registers 2 *
          longMulStackTestState.registers 3))
      (executeInstructions (zeroState 64)
        [.mulHU 5 2 3, .mul 6 2 3]) := by
  apply wordStackRegisterRelation_executeLongMul
  · intro register hregister
    rfl
  all_goals omega

end Flapjack.RiscV
