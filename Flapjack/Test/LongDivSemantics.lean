import Flapjack.RiscV.WordToStack

/-! Executable coverage for CakeML's normalized StackLang `LongDiv` operation.
    The low word is intentionally included in the dividend, so this catches
    implementations that accidentally treat the operation as ordinary `div`. -/

namespace Flapjack.RiscV

def longDivSemanticsState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 2 then BitVec.ofNat 8 2
      else if register = 3 then BitVec.ofNat 8 44
      else if register = 4 then BitVec.ofNat 8 5
      else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def longDivSemanticsResult : Option (WordStackMachineState 8) :=
  evalWordStackMachine longDivSemanticsState
    (.inst (.arith (.longDiv 0 1 2 3 4)))

#guard
  match longDivSemanticsResult with
  | some state =>
      state.registers 0 = BitVec.ofNat 8 111 &&
      state.registers 1 = BitVec.ofNat 8 1
  | none => false

def longDivSemanticsOverflowState : WordStackMachineState 8 :=
  { longDivSemanticsState with
    registers := fun register =>
      if register = 2 then BitVec.ofNat 8 1
      else if register = 3 then BitVec.ofNat 8 0
      else if register = 4 then BitVec.ofNat 8 1
      else 0 }

#guard
  (evalWordStackMachine longDivSemanticsOverflowState
    (.inst (.arith (.longDiv 0 1 2 3 4)))).isNone

def longDivSemanticsZeroDivisorState : WordStackMachineState 8 :=
  { longDivSemanticsState with
    registers := fun register =>
      if register = 4 then 0 else longDivSemanticsState.registers register }

#guard
  (evalWordStackMachine longDivSemanticsZeroDivisorState
    (.inst (.arith (.longDiv 0 1 2 3 4)))).isNone

end Flapjack.RiscV
