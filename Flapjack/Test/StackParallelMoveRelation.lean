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

end Flapjack.RiscV
