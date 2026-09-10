import Flapjack.RiscV.CorrectnessStackDynamicMemory
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression test for register-held StackRemove frame offsets. -/

namespace Flapjack.RiscV

example :
    WordStackRegisterRelationExceptRegister 29
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.stack 12))
      (executeInstructions (zeroState 64)
        [.add 29 20 6, .loadWord 5 29]) := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackLoadAny
    (config := config) (source := stackRiscVTestSource)
    (target := zeroState 64) (destination := 5)
    (offsetRegister := 6) (offset := 12)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (haddressScratch := by dsimp [config]; decide +kernel)
    (hoffsetRegister := by decide +kernel)
    (hdestination := by decide +kernel)
    (hdestinationNonzero := by decide +kernel)
    (haddressScratchNonzero := by dsimp [config]; decide +kernel)
    (hstackPointerAddressScratch := by dsimp [config]; decide +kernel)
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (hcell := by
      simp [stackRiscVTestSource, zeroState, readWordValue, readByte, byteAddress]
      decide +kernel)

end Flapjack.RiscV
