import Flapjack.RiscV.CorrectnessStackRemoveDynamic

/-!
# StackRemove bitmap-load semantics

The bitmap load first reads the bitmap-base store slot, adds a dynamic
address, scales the resulting bitmap index, and loads the selected word.
This theorem records that behavior in the word-machine model.
-/

namespace Flapjack.RiscV

theorem evalStackRemoveBitmapLoad [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination address : Nat)
    (haddressScratchStoreBase : config.addressScratch ≠ config.storeBase)
    (hdestinationScratch : destination ≠ config.scratch)
    (haddressDestination : address ≠ destination)
    (haddressAddressScratch : address ≠ config.addressScratch) :
    (evalWordStackMachine state
      (stackRemoveBitmapLoad config destination address)).map
        (fun final => final.registers destination) =
      some (state.memory
        ((state.memory
            (state.registers config.storeBase -
              BitVec.ofNat width
                (config.bytesInWord * stackStorePosition .bitmapBase)) +
          state.registers address) <<<
          shiftAmount (BitVec.ofNat width config.wordShift))) := by
  simp [stackRemoveBitmapLoad, stackRemoveGet, stackRemoveAddress,
    stackRemoveJoin, stackStorePosition, evalWordStackMachine,
    wordStackMachineBinOp, wordStackMachineShift,
    wordStackMachineWriteRegister, Ne.symm haddressScratchStoreBase,
    hdestinationScratch, haddressDestination, haddressAddressScratch]

end Flapjack.RiscV
