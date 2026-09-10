import Flapjack.RiscV.CorrectnessStackDelta
import Flapjack.Test.CorrectnessStackRiscV

/-! Regressions for one-chunk StackRemove frame allocation and release. -/

namespace Flapjack.RiscV

def stackDeltaTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackDeltaTestConfig 2 3 (.stackAlloc 2 : StackProg Nat) =
      some [.addi 31 0 (BitVec.ofNat 64 16), .sub 20 20 31] := by
  simpa [stackDeltaTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackAlloc_small (width := 64)
      { services := [] } stackDeltaTestConfig 2 3 2
      (by simp [stackDeltaTestConfig]) (by simp [stackDeltaTestConfig])
      (by decide +kernel))

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackDeltaTestConfig 2 3 (.stackFree 1 : StackProg Nat) =
      some [.addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31] := by
  simpa [stackDeltaTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackFree_small (width := 64)
      { services := [] } stackDeltaTestConfig 2 3 1
      (by simp [stackDeltaTestConfig]) (by simp [stackDeltaTestConfig])
      (by decide +kernel))

example :
    (executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 16), .sub 20 20 31]).registers 20 =
      (zeroState 64).registers 20 -
        BitVec.ofNat 64 16 := by
  refine executeStackRemoveStackAlloc_small
    (config := stackDeltaTestConfig) (target := zeroState 64) (words := 2)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hwords := by decide +kernel)
    (hzero := by simp [zeroState])

example :
    (executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31]).registers 20 =
      (zeroState 64).registers 20 +
        BitVec.ofNat 64 8 := by
  refine executeStackRemoveStackFree_small
    (config := stackDeltaTestConfig) (target := zeroState 64) (words := 1)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hwords := by decide +kernel)
    (hzero := by simp [zeroState])

example :
    (evalWordStackMachine stackRiscVTestSource
      (stackRemoveStackAlloc stackDeltaTestConfig 2)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some ((executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 16), .sub 20 20 31]).registers 20) := by
  apply compileStackProgramNatToRiscV_stackAlloc_small_eval_simulation
    (context := { services := [] }) (config := stackDeltaTestConfig)
    (sectionId := 2) (initialLabel := 3) (words := 2)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hwords := by decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (code := [.addi 31 0 (BitVec.ofNat 64 16), .sub 20 20 31])
    (hcode := by
      simpa [stackDeltaTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackAlloc_small (width := 64)
          { services := [] } stackDeltaTestConfig 2 3 2
          (by decide +kernel) (by decide +kernel) (by decide +kernel)))

example :
    (evalWordStackMachine stackRiscVTestSource
      (stackRemoveStackFree stackDeltaTestConfig 1)).map
        (fun final => final.registers stackDeltaTestConfig.stackPointer) =
      some ((executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31]).registers 20) := by
  apply compileStackProgramNatToRiscV_stackFree_small_eval_simulation
    (context := { services := [] }) (config := stackDeltaTestConfig)
    (sectionId := 2) (initialLabel := 3) (words := 1)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hscratchPointer := by decide +kernel)
    (hwords := by decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (code := [.addi 31 0 (BitVec.ofNat 64 8), .add 20 20 31])
    (hcode := by
      simpa [stackDeltaTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackFree_small (width := 64)
          { services := [] } stackDeltaTestConfig 2 3 1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)))

end Flapjack.RiscV
