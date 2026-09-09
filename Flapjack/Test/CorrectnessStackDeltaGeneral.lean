import Flapjack.RiscV.CorrectnessStackDeltaGeneral
import Flapjack.Test.CorrectnessStackDelta

/-! Regression for recursively split, arbitrary-size StackRemove allocation. -/

namespace Flapjack.RiscV

def stackDeltaGeneralMachineState : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    (evalWordStackMachine stackDeltaGeneralMachineState
      (stackRemoveStackAlloc stackDeltaTestConfig 256)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some (stackDeltaGeneralMachineState.registers stackDeltaTestConfig.stackPointer -
        BitVec.ofNat 64 (stackDeltaTestConfig.bytesInWord * 256)) := by
  exact evalStackRemoveStackAlloc_all stackDeltaTestConfig
    stackDeltaGeneralMachineState 256 (by decide)

example :
    (evalWordStackMachine stackDeltaGeneralMachineState
      (stackRemoveStackFree stackDeltaTestConfig 256)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some (stackDeltaGeneralMachineState.registers stackDeltaTestConfig.stackPointer +
        BitVec.ofNat 64 (stackDeltaTestConfig.bytesInWord * 256)) := by
  exact evalStackRemoveStackFree_all stackDeltaTestConfig
    stackDeltaGeneralMachineState 256 (by decide)

end Flapjack.RiscV
