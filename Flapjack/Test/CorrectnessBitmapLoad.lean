import Flapjack.RiscV.CorrectnessBitmapLoad

/-! Concrete RV64 regression for the bitmap-load machine contract. -/

namespace Flapjack.RiscV

def bitmapLoadTestConfig : StackRemoveConfig :=
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
        [.addi 29 0 (BitVec.ofNat 64 88), .sub 29 10 29,
         .loadWord 6 29, .add 6 6 7, .addi 31 0 (BitVec.ofNat 64 3),
         .sll 6 6 31, .loadWord 6 6]).registers 6 =
      readWordValue (zeroState 64)
        ((readWordValue (zeroState 64)
            ((zeroState 64).registers 10 - BitVec.ofNat 64 88) +
          (zeroState 64).registers 7) <<<
          shiftAmount (BitVec.ofNat 64 3)) := by
  refine executeStackRemoveBitmapLoad
    (config := bitmapLoadTestConfig) (target := zeroState 64)
    (destination := 6) (address := 7)
    (hstoreBase := by decide +kernel)
    (haddressScratch := by decide +kernel)
    (hdestination := by decide +kernel)
    (haddress := by decide +kernel)
    (hscratch := by decide +kernel)
    (hstoreBaseNonzero := by decide +kernel)
    (haddressScratchNonzero := by decide +kernel)
    (hdestinationNonzero := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (haddressScratchStoreBase := by decide +kernel)
    (hdestinationScratch := by decide +kernel)
    (haddressDestination := by decide +kernel)
    (haddressAddressScratch := by decide +kernel)
    (hzero := by simp [zeroState])

end Flapjack.RiscV
