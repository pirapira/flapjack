import Flapjack.RiscV.CorrectnessStackRemoveBitmap

/-! Regression check for the StackRemove bitmap-load contract. -/

namespace Flapjack.RiscV

example [NeZero width]
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
  exact evalStackRemoveBitmapLoad config state destination address
    haddressScratchStoreBase hdestinationScratch haddressDestination
    haddressAddressScratch

end Flapjack.RiscV
