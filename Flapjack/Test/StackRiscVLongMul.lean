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

def longMulStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    evalWordStackMachine longMulStackTestState
      (.inst (.arith (.longMul 5 6 2 3)) : StackProg Nat) =
      some (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister longMulStackTestState 5 0) 6 0) := by
  simpa [longMulStackTestState] using (evalWordStackMachine_longMul (width := 64)
    longMulStackTestState 5 6 2 3)

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      longMulStackRemoveConfig 2 3
      (.inst (.arith (.longMul 5 6 2 3)) : StackProg Nat) =
      some [.mulHU 5 2 3, .mul 6 2 3] := by
  simpa using (compileStackProgramNatToRiscV_longMul (width := 64)
    { services := [] } longMulStackRemoveConfig 2 3 5 6 2 3
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister longMulStackTestState 5 0) 6 0)
      (executeInstructions (zeroState 64) [.mulHU 5 2 3, .mul 6 2 3]) := by
  apply compileStackProgramNatToRiscV_longMul_register_simulation
    (width := 64) { services := [] } longMulStackRemoveConfig 2 3 5 6 2 3
    longMulStackTestState (zeroState 64)
    (by intro register hregister; rfl)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    [.mulHU 5 2 3, .mul 6 2 3]
  simpa using (compileStackProgramNatToRiscV_longMul (width := 64)
    { services := [] } longMulStackRemoveConfig 2 3 5 6 2 3
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

end Flapjack.RiscV
