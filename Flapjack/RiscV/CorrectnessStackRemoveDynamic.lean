import Flapjack.RiscV.CorrectnessStack

/-!
# Dynamic StackRemove memory contracts

The complete StackRemove pass uses the `Any` variants when a stack offset is
held in a register.  These contracts connect those emitted programs to the
word-memory model used by the RISC-V correctness proofs.
-/

namespace Flapjack.RiscV

theorem evalStackRemoveStackLoadAny [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination offsetRegister : Nat) :
    (evalWordStackMachine state
      (stackRemoveStackLoadAny config destination offsetRegister)).map
        (fun final => final.registers destination) =
      some (state.memory
        (state.registers config.stackPointer + state.registers offsetRegister)) := by
  simp [stackRemoveStackLoadAny, stackRemoveJoin, evalWordStackMachine,
    wordStackMachineBinOp, wordStackMachineWriteRegister]

theorem evalStackRemoveStackStoreAny [NeZero width]
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
  by_cases hmove : config.scratch = source
  · have hsourceAddress : source ≠ config.addressScratch := by
      intro hsource
      apply hscratchAddress
      exact hmove.trans hsource
    simp [stackRemoveStackStoreAny, stackRemoveMove, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hmove, hsourceAddress]
  · simp [stackRemoveStackStoreAny, stackRemoveMove, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      hmove, hscratchAddress, Ne.symm hscratchPointer,
      Ne.symm hscratchOffset]

theorem evalStackRemoveStackGetSize [NeZero width]
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
  by_cases hregisterScratch : register = config.scratch
  · simp [stackRemoveStackGetSize, stackRemoveStackDelta, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineShift, wordStackMachineWriteRegister,
      hregisterScratch, hscratchAddress, hregisterBase,
      hbaseScratch, hbaseAddress, Ne.symm hscratchAddress] <;>
      split <;> simp_all [evalWordStackMachine, wordStackMachineShift,
        wordStackMachineBinOp, wordStackMachineWriteRegister,
        Ne.symm hregisterBase]
  · simp [stackRemoveStackGetSize, stackRemoveStackDelta, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineShift, wordStackMachineWriteRegister,
      hregisterScratch, hscratchAddress, hregisterBase,
      hbaseScratch, hbaseAddress, Ne.symm hscratchAddress] <;>
      split <;> simp_all [evalWordStackMachine, wordStackMachineShift,
        wordStackMachineBinOp, wordStackMachineWriteRegister,
        Ne.symm hregisterBase]

theorem evalStackRemoveStackSetSize [NeZero width]
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
  by_cases hregisterScratch : register = config.scratch
  · simp [stackRemoveStackSetSize, stackRemoveStackDelta, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineShift, wordStackMachineWriteRegister,
      hregisterScratch, hscratchAddress, hstackPointerScratch,
      hstackPointerAddress, hregisterBase, hregisterPointer,
      hbaseScratch, hbaseAddress, Ne.symm hscratchAddress,
      Ne.symm hstackPointerScratch, Ne.symm hstackPointerAddress,
      Ne.symm hregisterBase] <;> split <;>
      simp_all [evalWordStackMachine, wordStackMachineShift,
        wordStackMachineBinOp, wordStackMachineWriteRegister]
  · simp [stackRemoveStackSetSize, stackRemoveStackDelta, stackRemoveMove,
      stackRemoveJoin, evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineShift, wordStackMachineWriteRegister,
      hregisterScratch, hscratchAddress, hstackPointerScratch,
      hstackPointerAddress, hregisterBase, hregisterPointer,
      hbaseScratch, hbaseAddress, Ne.symm hscratchAddress,
      Ne.symm hstackPointerScratch, Ne.symm hstackPointerAddress,
      Ne.symm hregisterBase] <;> split <;>
      simp_all [evalWordStackMachine, wordStackMachineShift,
        wordStackMachineBinOp, wordStackMachineWriteRegister]

end Flapjack.RiscV
