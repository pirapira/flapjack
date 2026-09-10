import Flapjack.StackAlloc.Machine

/-! StackLang LocValue uses the code environment for validation and stores an
    abstract code pointer.  The later LabLang pass replaces the label by its
    laid-out instruction position. -/

namespace Flapjack.RiscV

def locValueMachineState : WordStackMachineState 8 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def locValueMachineCode : Nat → Option (StackProg Nat)
  | 20 => some .skip
  | _ => none

example :
    evalStackProgFuelWithCode 1 locValueMachineCode locValueMachineState
      (.locValue 5 20 0) =
      some (.normal (wordStackMachineWriteRegister locValueMachineState 5
        (BitVec.ofNat 8 20))) := by
  simp [evalStackProgFuelWithCode, locValueMachineCode]

example :
    evalStackProgFuelWithCode 1 locValueMachineCode locValueMachineState
      (.locValue 5 21 0) = none := by
  simp [evalStackProgFuelWithCode, locValueMachineCode]

end Flapjack.RiscV
