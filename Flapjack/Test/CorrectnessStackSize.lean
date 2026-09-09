import Flapjack.RiscV.CorrectnessStackSize
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression for StackRemove frame-size lowering on RISC-V. -/

namespace Flapjack.RiscV

example :
    (executeInstructions (zeroState 64)
        [.or 6 20 20, .sub 6 6 21, .ori 31 0 (BitVec.ofNat 64 3),
         .srl 6 6 31]).registers 6 =
      BitVec.ushiftRight
        ((zeroState 64).registers 20 - (zeroState 64).registers 21)
        (shiftAmount (BitVec.ofNat 64 3)) := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackGetSize
    (config := config) (target := zeroState 64) (register := 6)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (hstackBase := by dsimp [config]; decide +kernel)
    (hscratch := by dsimp [config]; decide +kernel)
    (hregister := by decide +kernel)
    (hregisterNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (hstackPointerScratch := by dsimp [config]; decide +kernel)
    (hregisterScratch := by dsimp [config]; decide +kernel)
    (hregisterBase := by dsimp [config]; decide +kernel)
    (hzero := by simp [zeroState])

end Flapjack.RiscV
