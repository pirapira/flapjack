import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# Immediate shifts at the RISC-V boundary

The Word backend selects the immediate RISC-V shift forms for a variable
shifted by a constant.  These contracts connect those instructions to the
StackLang shift operation while retaining the common register relation.
-/

namespace Flapjack.RiscV

theorem wordStackRegisterRelation_executeSlli
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (amount : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsl (source.registers sourceRegister) amount))
      (execute target (.slli ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ amount)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.shiftLeft (source.registers sourceRegister) (shiftAmount amount)))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.shiftLeft (target.registers ⟨sourceRegister, hsource⟩)
        (shiftAmount amount)))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.shiftLeft (source.registers sourceRegister) (shiftAmount amount)) hrel
    hdestination hdestinationNonzero

theorem wordStackRegisterRelation_executeSrli
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (amount : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsr (source.registers sourceRegister) amount))
      (execute target (.srli ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ amount)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.ushiftRight (source.registers sourceRegister) (shiftAmount amount)))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.ushiftRight (target.registers ⟨sourceRegister, hsource⟩)
        (shiftAmount amount)))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.ushiftRight (source.registers sourceRegister) (shiftAmount amount)) hrel
    hdestination hdestinationNonzero

theorem wordStackRegisterRelation_executeSrai
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (amount : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .asr (source.registers sourceRegister) amount))
      (execute target (.srai ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ amount)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.sshiftRight (source.registers sourceRegister) (shiftAmount amount)))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.sshiftRight (target.registers ⟨sourceRegister, hsource⟩)
        (shiftAmount amount)))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.sshiftRight (source.registers sourceRegister) (shiftAmount amount)) hrel
    hdestination hdestinationNonzero

theorem compileWordImmediateShiftLsl_sound [NeZero width]
    (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .lsl (.var 2) (.const amount))) =
      some (execute state (.slli 1 2 amount)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

theorem compileWordImmediateShiftLsr_sound [NeZero width]
    (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .lsr (.var 2) (.const amount))) =
      some (execute state (.srli 1 2 amount)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

theorem compileWordImmediateShiftAsr_sound [NeZero width]
    (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .asr (.var 2) (.const amount))) =
      some (execute state (.srai 1 2 amount)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

end Flapjack.RiscV
