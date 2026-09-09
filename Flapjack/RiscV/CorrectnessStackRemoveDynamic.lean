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

end Flapjack.RiscV
