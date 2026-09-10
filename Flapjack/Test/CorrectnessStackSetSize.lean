import Flapjack.RiscV.CorrectnessStackSetSize
import Flapjack.Test.CorrectnessStackRiscV

/-! Regressions for both StackRemove frame-size setter shift layouts. -/

namespace Flapjack.RiscV

def stackSetSizeTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example :
    (executeInstructions (zeroState 64)
        [.ori 31 0 (BitVec.ofNat 64 3), .sll 6 6 31,
         .or 20 21 21, .add 20 20 6]).registers 20 =
      (zeroState 64).registers 21 +
        BitVec.shiftLeft ((zeroState 64).registers 6)
          (shiftAmount (BitVec.ofNat 64 3)) := by
  refine executeStackRemoveStackSetSize
    (config := stackSetSizeTestConfig) (target := zeroState 64) (register := 6)
    (hstackPointer := by decide +kernel)
    (hstackBase := by decide +kernel)
    (hscratch := by decide +kernel)
    (haddressScratch := by decide +kernel)
    (hregister := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hstackBaseNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (haddressScratchNonzero := by decide +kernel)
    (hregisterNonzero := by decide +kernel)
    (hregisterBase := by decide +kernel)
    (hregisterPointer := by decide +kernel)
    (hbaseScratch := by decide +kernel)
    (hbaseAddress := by decide +kernel)
    (hscratchAddress := by decide +kernel)
    (hzero := by simp [zeroState])

example :
    (executeInstructions (zeroState 64)
        [.ori 29 0 (BitVec.ofNat 64 3), .sll 31 31 29,
         .or 20 21 21, .add 20 20 31]).registers 20 =
      (zeroState 64).registers 21 +
        BitVec.shiftLeft ((zeroState 64).registers 31)
          (shiftAmount (BitVec.ofNat 64 3)) := by
  refine executeStackRemoveStackSetSize
    (config := stackSetSizeTestConfig) (target := zeroState 64) (register := 31)
    (hstackPointer := by decide +kernel)
    (hstackBase := by decide +kernel)
    (hscratch := by decide +kernel)
    (haddressScratch := by decide +kernel)
    (hregister := by decide +kernel)
    (hstackPointerNonzero := by decide +kernel)
    (hstackBaseNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (haddressScratchNonzero := by decide +kernel)
    (hregisterNonzero := by decide +kernel)
    (hregisterBase := by decide +kernel)
    (hregisterPointer := by decide +kernel)
    (hbaseScratch := by decide +kernel)
    (hbaseAddress := by decide +kernel)
    (hscratchAddress := by decide +kernel)
    (hzero := by simp [zeroState])

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVRemoveConfig 2 3 (.stackSetSize 6 : StackProg Nat) =
      some [.addi 31 0 (BitVec.ofNat 64 3), .sll 6 6 31,
        .or 20 21 21, .add 20 20 6] := by
  simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackSetSize (width := 64)
      { services := [] } stackRiscVRemoveConfig 2 3 6
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
      (by omega))

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVRemoveConfig 2 3 (.stackSetSize 31 : StackProg Nat) =
      some [.addi 29 0 (BitVec.ofNat 64 3), .sll 31 31 29,
        .or 20 21 21, .add 20 20 31] := by
  simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackSetSize (width := 64)
      { services := [] } stackRiscVRemoveConfig 2 3 31
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by omega))

example :
    (evalWordStackMachine stackRiscVTestSource
      (stackRemoveStackSetSize stackRiscVRemoveConfig 6)).map
        (fun final => final.registers stackRiscVRemoveConfig.stackPointer) =
      some ((executeInstructions (zeroState 64)
        [.addi 31 0 (BitVec.ofNat 64 3), .sll 6 6 31,
         .or 20 21 21, .add 20 20 6]).registers 20) := by
  apply compileStackProgramNatToRiscV_stackSetSize_eval_simulation
    (context := { services := [] }) (config := stackRiscVRemoveConfig)
    (sectionId := 2) (initialLabel := 3) (register := 6)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by simp [stackRiscVRemoveConfig])
    (hstackBase := by simp [stackRiscVRemoveConfig])
    (hscratch := by simp [stackRiscVRemoveConfig])
    (haddressScratch := by simp [stackRiscVRemoveConfig])
    (hregister := by omega)
    (hstackPointerNonzero := by simp [stackRiscVRemoveConfig])
    (hstackBaseNonzero := by simp [stackRiscVRemoveConfig])
    (hscratchNonzero := by simp [stackRiscVRemoveConfig])
    (haddressScratchNonzero := by simp [stackRiscVRemoveConfig])
    (hregisterNonzero := by omega)
    (hstackPointerScratch := by simp [stackRiscVRemoveConfig])
    (hstackPointerAddress := by simp [stackRiscVRemoveConfig])
    (hregisterBase := by simp [stackRiscVRemoveConfig])
    (hregisterPointer := by simp [stackRiscVRemoveConfig])
    (hbaseScratch := by simp [stackRiscVRemoveConfig])
    (hbaseAddress := by simp [stackRiscVRemoveConfig])
    (hscratchAddress := by simp [stackRiscVRemoveConfig])
    (hzero := by simp [zeroState])
    (hrel := by
      intro register hregister
      simp [stackRiscVTestSource, zeroState])
    (code := [.addi 31 0 (BitVec.ofNat 64 3), .sll 6 6 31,
      .or 20 21 21, .add 20 20 6])
    (hcode := by
      simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackSetSize (width := 64)
          { services := [] } stackRiscVRemoveConfig 2 3 6
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by omega)))

end Flapjack.RiscV
