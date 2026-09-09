import Flapjack.RiscV.CorrectnessStackRiscV

/-! Concrete smoke test for the StackLang-to-RISC-V register relation. -/

namespace Flapjack.RiscV

def stackRiscVTestSource : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

theorem stackRiscVTestRelation :
    WordStackRegisterRelation stackRiscVTestSource (zeroState 64) := by
  intro register hregister
  simp [stackRiscVTestSource, zeroState]

example :
    (labCompilePlain (.const 5 7 : LabPlain (Word 64))).bind
        (fun code =>
          some (WordStackRegisterRelation
            (wordStackMachineWriteRegister stackRiscVTestSource 5
              (BitVec.ofNat 64 7))
            (executeInstructions (zeroState 64) code))) =
      some (WordStackRegisterRelation
        (wordStackMachineWriteRegister stackRiscVTestSource 5
          (BitVec.ofNat 64 7))
        (execute (zeroState 64) (.addi 5 0 (BitVec.ofNat 64 7)))) := by
  exact labCompilePlain_const_register_simulation stackRiscVTestSource
    (zeroState 64) 5 7 stackRiscVTestRelation (by omega) (by omega)
    (by simp [stackRiscVTestSource])

end Flapjack.RiscV
