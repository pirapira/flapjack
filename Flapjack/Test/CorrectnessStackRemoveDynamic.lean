import Flapjack.RiscV.CorrectnessStackRemoveDynamic

/-! Regression checks for dynamic StackRemove load/store contracts. -/

namespace Flapjack.RiscV

example [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination offsetRegister : Nat) :
    (evalWordStackMachine state
      (stackRemoveStackLoadAny config destination offsetRegister)).map
        (fun final => final.registers destination) =
      some (state.memory
        (state.registers config.stackPointer + state.registers offsetRegister)) := by
  exact evalStackRemoveStackLoadAny config state destination offsetRegister

example [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source offsetRegister : Nat)
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hscratchOffset : config.scratch ≠ offsetRegister) :
    (evalWordStackMachine state
      (stackRemoveStackStoreAny config source offsetRegister)).map
        (fun final =>
          final.memory
            (state.registers config.stackPointer + state.registers offsetRegister)) =
      some (state.registers source) := by
  exact evalStackRemoveStackStoreAny config state source offsetRegister
    hscratchAddress hscratchPointer hscratchOffset

example [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (register : Nat)
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hregisterBase : register ≠ config.stackBase)
    (hbaseScratch : config.stackBase ≠ config.scratch)
    (hbaseAddress : config.stackBase ≠ config.addressScratch) :
    (evalWordStackMachine state
      (stackRemoveStackGetSize config register)).map
        (fun final => final.registers register) =
      some (BitVec.ushiftRight
        (state.registers config.stackPointer - state.registers config.stackBase)
        (shiftAmount (BitVec.ofNat width config.wordShift))) := by
  exact evalStackRemoveStackGetSize config state register hscratchAddress hregisterBase
    hbaseScratch hbaseAddress

example [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (register : Nat)
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddress : config.stackPointer ≠ config.addressScratch)
    (hregisterBase : register ≠ config.stackBase)
    (hregisterPointer : register ≠ config.stackPointer)
    (hbaseScratch : config.stackBase ≠ config.scratch)
    (hbaseAddress : config.stackBase ≠ config.addressScratch) :
    (evalWordStackMachine state
      (stackRemoveStackSetSize config register)).map
        (fun final => final.registers config.stackPointer) =
      some (state.registers config.stackBase +
        BitVec.shiftLeft (state.registers register)
          (shiftAmount (BitVec.ofNat width config.wordShift))) := by
  exact evalStackRemoveStackSetSize config state register hscratchAddress
    hstackPointerScratch hstackPointerAddress hregisterBase hregisterPointer
    hbaseScratch hbaseAddress

end Flapjack.RiscV
