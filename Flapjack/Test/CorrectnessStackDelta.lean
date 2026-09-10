import Flapjack.RiscV.CorrectnessStackDelta

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

end Flapjack.RiscV
