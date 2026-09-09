import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# Immediate bitwise expressions at the RISC-V boundary

The Word backend selects the immediate RISC-V forms for a variable combined
with a constant.  These equations connect those forms to the same register
relation used by the StackLang correctness layer.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordStackRegisterRelation_executeAndi
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (immediate : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers sourceRegister &&& immediate))
      (execute target (.andi ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ immediate)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers sourceRegister &&& immediate))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨sourceRegister, hsource⟩ &&& immediate))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers sourceRegister &&& immediate) hrel
    hdestination hdestinationNonzero

theorem wordStackRegisterRelation_executeOri
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (immediate : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers sourceRegister ||| immediate))
      (execute target (.ori ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ immediate)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers sourceRegister ||| immediate))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨sourceRegister, hsource⟩ ||| immediate))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers sourceRegister ||| immediate) hrel
    hdestination hdestinationNonzero

theorem wordStackRegisterRelation_executeXori
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (immediate : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers sourceRegister ^^^ immediate))
      (execute target (.xori ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ immediate)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers sourceRegister ^^^ immediate))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨sourceRegister, hsource⟩ ^^^ immediate))
  rw [hsourceValue]
  exact wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers sourceRegister ^^^ immediate) hrel
    hdestination hdestinationNonzero

theorem compileWordImmediateAnd_sound [NeZero width] (state : State width)
    (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .and [.var 2, .const value])) =
      some (execute state (.andi 1 2 value)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

theorem compileWordImmediateOr_sound [NeZero width] (state : State width)
    (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .or [.var 2, .const value])) =
      some (execute state (.ori 1 2 value)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

theorem compileWordImmediateXor_sound [NeZero width] (state : State width)
    (value : Word width) :
    evalWordProg state
        (.assign 1 (.op .xor [.var 2, .const value])) =
      some (execute state (.xori 1 2 value)) := by
  simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
    registerOfNat, executeInstructions, execute, writeRegister, nextPc]

end Flapjack.RiscV
