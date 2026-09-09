import Flapjack.RiscV.CorrectnessStackStore
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression test for the scratch-aliasing StackRemove stack-store path. -/

namespace Flapjack.RiscV

example :
    (executeInstructions (zeroState 64)
        [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + BitVec.ofNat 64 (8 * 12))
        (stackRiscVTestSource.registers 31)).memory := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackStore_same_memory
    (config := config) (source := stackRiscVTestSource)
    (target := zeroState 64) (register := 31) (offset := 12)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (haddressScratch := by dsimp [config]; decide +kernel)
    (hscratchRegister := by dsimp [config]; decide +kernel)
    (haddressScratchNonzero := by dsimp [config]; decide +kernel)
    (hstackPointerAddressScratch := by dsimp [config]; decide +kernel)
    (hscratchAddressScratch := by dsimp [config]; decide +kernel)
    (hvalue := by simp [stackRiscVTestSource, zeroState])
    (hzero := by simp [zeroState])

end Flapjack.RiscV
