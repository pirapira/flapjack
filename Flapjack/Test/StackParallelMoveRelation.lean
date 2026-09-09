import Flapjack.RiscV.CorrectnessStackParallelMove

/-! Regression coverage for the singleton physical parallel-move boundary. -/

namespace Flapjack.RiscV

def parallelMoveConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    addressScratch := 30
    stackBase := 8 }

def parallelMoveState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 17 else 0
    stack := fun slot => if slot = 11 then BitVec.ofNat 8 23 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def entryMoveConfig : WordStackConfig :=
  { locations := [(1, .register 5)]
    scratch := 31
    addressScratch := 30
    stackBase := 8 }

def entryMoveState : WordStackMachineState 8 :=
  { registers := fun register => if register = 2 then BitVec.ofNat 8 17 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    wordStackParallelLocationMove (α := Nat) parallelMoveConfig
      [(.register 5, .register 6)] =
      some (.arith .or 5 6 6 : StackProg Nat) := by
  simp [wordStackParallelLocationMove, wordStackParallelLocationMoveAux,
    wordStackLocationMoveDestinations, wordStackLocationMoveReady,
    wordStackLocationMoveRemoveDestination, wordStackLocationMove,
    wordStackJoin, parallelMoveConfig]

example :
    wordStackLocationValue parallelMoveConfig
      (wordStackMachineWriteRegister parallelMoveState 5
        (BitVec.ofNat 8 17)) (.register 5) =
      wordStackLocationValue parallelMoveConfig parallelMoveState (.register 6) := by
  apply evalWordStackMachine_parallelLocationMove_singleton_preserves_value
    (hdestinationScratch := by simp [parallelMoveConfig])
    (hdestinationAddressScratch := by simp [parallelMoveConfig])
    (hsourceScratch := by simp [parallelMoveConfig])
    (hsourceAddressScratch := by simp [parallelMoveConfig])
  simp [parallelMoveConfig, parallelMoveState, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMove, wordStackJoin, evalWordStackMachine,
    wordStackMachineWriteRegister, wordStackMachineBinOp]

example :
    wordStackMovesFromPhysical (α := Nat) entryMoveConfig [1] 2 =
      some (.arith .or 5 2 2 : StackProg Nat) := by
  simp [entryMoveConfig, wordStackMovesFromPhysical,
    wordStackPhysicalMovesFrom, wordStackParallelLocationMove,
    wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
    wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
    wordStackLocationMove, wordStackJoin, wordStackLocation, lookupNatInfo]

example :
    wordStackLocationValue entryMoveConfig
      (wordStackMachineWriteRegister entryMoveState 5
        (BitVec.ofNat 8 17)) (.register 5) =
      wordStackLocationValue entryMoveConfig entryMoveState (.register 2) := by
  apply evalWordStackMachine_movesFromPhysical_singleton_preserves_value
    (destination := 1) (source := 2) (destinationLocation := .register 5)
  · simp [entryMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [entryMoveConfig]
  · simp [entryMoveConfig]
  · simp [entryMoveConfig]
  · simp [entryMoveConfig]
  · simp [entryMoveConfig, entryMoveState, wordStackMovesFromPhysical,
      wordStackPhysicalMovesFrom, wordStackLocation, lookupNatInfo,
      wordStackParallelLocationMove,
      wordStackParallelLocationMoveAux, wordStackLocationMoveDestinations,
      wordStackLocationMoveReady, wordStackLocationMoveRemoveDestination,
      wordStackLocationMove, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineBinOp]

end Flapjack.RiscV
