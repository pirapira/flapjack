import Flapjack.RiscV.CorrectnessStackMemory
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression test for the StackRemove-to-RISC-V byte-memory boundary. -/

namespace Flapjack.RiscV

example :
    WordStackRegisterRelationExceptRegister 29
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.stack 12))
      (executeInstructions (zeroState 64)
        [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .loadWord 5 29]) := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackLoad
    (config := config)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (destination := 5) (offset := 12)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (haddressScratch := by dsimp [config]; decide +kernel)
    (hdestination := by decide +kernel)
    (hdestinationNonzero := by decide +kernel)
    (haddressScratchNonzero := by dsimp [config]; decide +kernel)
    (hstackPointerScratch := by dsimp [config]; decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (hcell := by
      unfold WordStackStackCellRelation
      simp [stackRiscVTestSource, zeroState, readWordValue, readByte, byteAddress]
      decide +kernel)

end Flapjack.RiscV
