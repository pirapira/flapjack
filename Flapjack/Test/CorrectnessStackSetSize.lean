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

end Flapjack.RiscV
