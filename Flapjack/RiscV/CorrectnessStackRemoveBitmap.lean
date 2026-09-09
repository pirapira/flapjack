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
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hdestinationScratch : destination ≠ config.scratch)
    (hdestinationAddress : destination ≠ config.addressScratch)
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
    wordStackMachineWriteRegister, haddressScratchStoreBase,
    hscratchAddress, hdestinationScratch, hdestinationAddress,
    haddressDestination, haddressAddressScratch,
    Ne.symm haddressScratchStoreBase, Ne.symm hscratchAddress,
    Ne.symm hdestinationScratch, Ne.symm hdestinationAddress,
    Ne.symm haddressDestination, Ne.symm haddressAddressScratch]

end Flapjack.RiscV
