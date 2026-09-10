import Flapjack.RiscV.CorrectnessStackRiscVDivision

/-! Regression coverage for StackLang unsigned division lowering. -/

namespace Flapjack.RiscV

open Flapjack

example :
    labCompilePlain
      (.word (.arith (.div 5 2 3)) : LabPlain (Word 64)) =
      some [.divU 5 2 3] := by
  exact labCompilePlain_div 5 2 3 (by omega) (by omega) (by omega)

def stackRiscVDivisionSource : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

theorem stackRiscVDivisionRelation :
    WordStackRegisterRelation stackRiscVDivisionSource (zeroState 64) := by
  intro register hregister
  simp [stackRiscVDivisionSource, zeroState]

def stackRiscVDivisionRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    evalWordStackMachine stackRiscVDivisionSource
      (.inst (.arith (.div 5 2 3)) : StackProg Nat) =
      some (wordStackMachineWriteRegister stackRiscVDivisionSource 5
        (BitVec.ofNat 64 (2 ^ 64 - 1))) := by
  rw [evalWordStackMachine_div]
  simp [stackRiscVDivisionSource]

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVDivisionRemoveConfig 2 3
      (.inst (.arith (.div 5 2 3)) : StackProg Nat) =
      some [.divU 5 2 3] := by
  simpa using (compileStackProgramNatToRiscV_div (width := 64)
    { services := [] } stackRiscVDivisionRemoveConfig 2 3 5 2 3
    (by omega) (by omega) (by omega))

example :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister stackRiscVDivisionSource 5
        (BitVec.ofNat 64 (2 ^ 64 - 1)))
      (executeInstructions (zeroState 64) [.divU 5 2 3]) := by
  apply compileStackProgramNatToRiscV_div_register_simulation
    (width := 64) { services := [] } stackRiscVDivisionRemoveConfig 2 3 5 2 3
    stackRiscVDivisionSource (zeroState 64) stackRiscVDivisionRelation
    (by omega) (by omega) (by omega) (by omega) [.divU 5 2 3]
  simpa using (compileStackProgramNatToRiscV_div (width := 64)
    { services := [] } stackRiscVDivisionRemoveConfig 2 3 5 2 3
    (by omega) (by omega) (by omega))

end Flapjack.RiscV
