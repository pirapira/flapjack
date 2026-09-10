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

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackDeltaTestConfig 2 3 (.stackAlloc 256 : StackProg Nat) =
      some [.addi 31 0 (BitVec.ofNat 64 2040), .sub 20 20 31,
        .addi 31 0 (BitVec.ofNat 64 8), .sub 20 20 31] := by
  simpa [stackDeltaTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackAlloc_256 (width := 64)
      { services := [] } stackDeltaTestConfig 2 3
      (by simp [stackDeltaTestConfig]) (by simp [stackDeltaTestConfig]))

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackDeltaTestConfig 2 3 (.stackFree 256 : StackProg Nat) =
      some [.addi 31 0 (BitVec.ofNat 64 2040), .add 20 20 31,
        .addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31] := by
  simpa [stackDeltaTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackFree_256 (width := 64)
      { services := [] } stackDeltaTestConfig 2 3
      (by simp [stackDeltaTestConfig]) (by simp [stackDeltaTestConfig]))

example :
    (evalWordStackMachine stackDeltaGeneralMachineState
      (stackRemoveStackAlloc stackDeltaTestConfig 256)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some ((executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 2040), .sub 20 20 31,
         .addi 31 0 (BitVec.ofNat 64 8), .sub 20 20 31]).registers 20) := by
  apply compileStackProgramNatToRiscV_stackAlloc_256_eval_simulation
    (context := { services := [] }) (config := stackDeltaTestConfig)
    (sectionId := 2) (initialLabel := 3)
    (source := stackDeltaGeneralMachineState) (target := zeroState 64)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackDeltaGeneralMachineState, zeroState])
    (code := [.addi 31 0 (BitVec.ofNat 64 2040), .sub 20 20 31,
      .addi 31 0 (BitVec.ofNat 64 8), .sub 20 20 31])
    (hcode := by
      simpa [stackDeltaTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackAlloc_256 (width := 64)
          { services := [] } stackDeltaTestConfig 2 3
          (by decide +kernel) (by decide +kernel)))

example :
    (evalWordStackMachine stackDeltaGeneralMachineState
      (stackRemoveStackFree stackDeltaTestConfig 256)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some ((executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 2040), .add 20 20 31,
         .addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31]).registers 20) := by
  apply compileStackProgramNatToRiscV_stackFree_256_eval_simulation
    (context := { services := [] }) (config := stackDeltaTestConfig)
    (sectionId := 2) (initialLabel := 3)
    (source := stackDeltaGeneralMachineState) (target := zeroState 64)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackDeltaGeneralMachineState, zeroState])
    (code := [.addi 31 0 (BitVec.ofNat 64 2040), .add 20 20 31,
      .addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31])
    (hcode := by
      simpa [stackDeltaTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackFree_256 (width := 64)
          { services := [] } stackDeltaTestConfig 2 3
          (by decide +kernel) (by decide +kernel)))

end Flapjack.RiscV
