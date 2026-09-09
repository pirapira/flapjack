import Flapjack.RiscV.CorrectnessSpill

/-! Regression coverage for the physical location boundary used by the
    spill-aware function-entry lowering. -/

namespace Flapjack.RiscV

def locationMoveConfig : WordStackConfig :=
  { locations := []
    scratch := 31
    addressScratch := 30
    stackBase := 8 }

def locationMoveState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 17 else 0
    stack := fun slot => if slot = 11 then BitVec.ofNat 8 23 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    wordStackLocationValue locationMoveConfig
      (wordStackMachineWriteRegister locationMoveState 5
        (BitVec.ofNat 8 17)) (.register 5) =
      wordStackLocationValue locationMoveConfig locationMoveState (.register 6) := by
  apply evalWordStackMachine_locationMove_preserves_value
  simp [locationMoveState, wordStackLocationMove, evalWordStackMachine,
    wordStackMachineWriteRegister, wordStackMachineBinOp]

example :
    wordStackLocationValue locationMoveConfig
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister locationMoveState 31
          (BitVec.ofNat 8 23)) 5 (BitVec.ofNat 8 23)) (.register 5) =
      wordStackLocationValue locationMoveConfig locationMoveState (.stack 3) := by
  apply evalWordStackMachine_locationMove_preserves_value
  simp [locationMoveConfig, locationMoveState, wordStackLocationMove,
    wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
    wordStackMachineBinOp]

end Flapjack.RiscV
