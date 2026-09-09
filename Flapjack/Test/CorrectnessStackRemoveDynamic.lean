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

end Flapjack.RiscV
