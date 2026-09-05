import Flapjack.RiscV.WordToStack
import Flapjack.StackRemove

/-!
Semantic correctness for the first StackRemove store equation.

The abstract WordStack machine models the runtime store as a separate map and
the lowered program as word-addressed memory.  The theorem below states the
invariant needed to connect those views for a non-`CurrHeap` store.
-/

namespace Flapjack.RiscV

theorem evalStackRemoveGet [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination : Nat) (store : StackStore)
    (hstore : store ≠ .currHeap)
    (haddress : config.addressScratch ≠ config.storeBase)
    (hmemory :
      state.memory
          (state.registers config.storeBase +
            BitVec.ofNat width (stackStorePosition store)) =
        state.stores store) :
    (evalWordStackMachine state (stackRemoveGet config destination store)).map
        (fun final => final.registers destination) =
      some (state.stores store) := by
  cases store <;>
    simp_all [stackRemoveGet, stackRemoveAddress, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, haddress, Ne.symm haddress]

theorem evalStackRemoveSet [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source : Nat) (store : StackStore)
    (hstore : store ≠ .currHeap)
    (haddress : config.addressScratch ≠ config.storeBase)
    (hsource : config.addressScratch ≠ source) :
    (evalWordStackMachine state (stackRemoveSet config store source)).map
        (fun final =>
          final.memory
            (state.registers config.storeBase +
              BitVec.ofNat width (stackStorePosition store))) =
      some (state.registers source) := by
  cases store <;>
    simp_all [stackRemoveSet, stackRemoveAddress, stackRemoveJoin,
      evalWordStackMachine, wordStackMachineBinOp,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      haddress, Ne.symm haddress, hsource, Ne.symm hsource]

theorem evalStackRemoveGetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (destination : Nat) :
    (evalWordStackMachine state
      (stackRemoveGet config destination .currHeap)).map
        (fun final => final.registers destination) =
      some (state.registers config.currHeap) := by
  simp [stackRemoveGet, evalWordStackMachine, wordStackMachineBinOp,
    wordStackMachineWriteRegister]

theorem evalStackRemoveSetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (state : WordStackMachineState width)
    (source : Nat) :
    (evalWordStackMachine state
      (stackRemoveSet config .currHeap source)).map
        (fun final => final.registers config.currHeap) =
      some (state.registers source) := by
  simp [stackRemoveSet, evalWordStackMachine, wordStackMachineBinOp,
    wordStackMachineWriteRegister]

end Flapjack.RiscV
