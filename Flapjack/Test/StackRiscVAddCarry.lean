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

def addCarryStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    evalWordStackMachine addCarryStackTestState
      (.inst (.arith (.addCarry 5 6 2 3 4)) : StackProg Nat) =
      some (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister addCarryStackTestState 5
          (addCarryWords (addCarryStackTestState.registers 2)
            (addCarryStackTestState.registers 3)
            (addCarryStackTestState.registers 4)).1)
        6
          (addCarryWords (addCarryStackTestState.registers 2)
            (addCarryStackTestState.registers 3)
            (addCarryStackTestState.registers 4)).2) := by
  exact evalWordStackMachine_addCarry (width := 64)
    addCarryStackTestState 5 6 2 3 4

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      addCarryStackRemoveConfig 2 3
      (.inst (.arith (.addCarry 5 6 2 3 4)) : StackProg Nat) =
      some [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
        .sltu 31 5 31, .or 6 6 31] := by
  simpa using (compileStackProgramNatToRiscV_addCarry (width := 64)
    { services := [] } addCarryStackRemoveConfig 2 3 5 6 2 3 4
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega))

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
  apply compileStackProgramNatToRiscV_addCarry_register_simulation
    (width := 64) { services := [] } addCarryStackRemoveConfig 2 3 5 6 2 3 4
    addCarryStackTestState (zeroState 64)
    (by intro register hregister hscratch; rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rfl)
    [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
      .sltu 31 5 31, .or 6 6 31]
  simpa using (compileStackProgramNatToRiscV_addCarry (width := 64)
    { services := [] } addCarryStackRemoveConfig 2 3 5 6 2 3 4
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega))

end Flapjack.RiscV
