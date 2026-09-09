import Flapjack.RiscV.CorrectnessStackFunctionEntry

/-! Regression coverage for sequencing a physical entry move and Word body. -/

namespace Flapjack.RiscV

def functionEntryConfig : WordStackConfig :=
  { locations := [(1, .register 5)]
    scratch := 31
    addressScratch := 30
    stackBase := 8 }

def functionEntryState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 2 then BitVec.ofNat 8 17 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def functionEntryFinal : WordStackMachineState 8 :=
  wordStackMachineWriteRegister functionEntryState 5 (BitVec.ofNat 8 17)

example :
    evalWordStackMachine functionEntryState
      (.arith .or 5 2 2 : StackProg Nat) = some functionEntryFinal := by
  simp [functionEntryState, functionEntryFinal, evalWordStackMachine,
    wordStackMachineWriteRegister, wordStackMachineBinOp]

example :
    evalWordStackMachine functionEntryState
      (wordStackJoin (.arith .or 5 2 2) (.skip : StackProg Nat)) =
      some functionEntryFinal := by
  apply evalWordStackMachine_wordStackJoin (middle := functionEntryFinal)
  · simp [functionEntryState, functionEntryFinal, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineBinOp]
  · simp [functionEntryFinal, evalWordStackMachine]

end Flapjack.RiscV
