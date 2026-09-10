import Flapjack.RiscV.CorrectnessStack
import Flapjack.RiscV.Lab

/-!
# StackLang register simulation at the RISC-V boundary

`WordStackMachineState` numbers registers with `Nat`, while the RISC-V model
uses the architectural `Fin 32` register file.  This module records the
smallest useful bridge: agreement on all architectural registers.  The first
contract connects StackLang's constant instruction with the exact `addi`
sequence emitted by LabLang and the RISC-V backend.
-/

namespace Flapjack.RiscV

def WordStackRegisterRelation [NeZero width]
    (source : WordStackMachineState width) (target : State width) : Prop :=
  ∀ register (hregister : register < 32),
    target.registers ⟨register, hregister⟩ = source.registers register

def WordStackRegisterRelationExceptX31 [NeZero width]
    (source : WordStackMachineState width) (target : State width) : Prop :=
  ∀ register (hregister : register < 32), register ≠ 31 →
    target.registers ⟨register, hregister⟩ = source.registers register

theorem wordStackRegisterRelation_writeRegister
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination : Nat) (value : Word width)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination value)
      (writeRegister target ⟨destination, hdestination⟩ value) := by
  intro register hregister
  have htarget := hrel register hregister
  have hdestinationFin : (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  by_cases hsame : register = destination
  · subst register
    simp [wordStackMachineWriteRegister, writeRegister, hdestinationFin]
  · have hfin : (⟨register, hregister⟩ : Fin 32) ≠
        ⟨destination, hdestination⟩ := by
      intro heq
      apply hsame
      exact congrArg Fin.val heq
    simp only [wordStackMachineWriteRegister, writeRegister,
      if_neg hdestinationFin, if_neg hfin, if_neg hsame]
    exact htarget

theorem wordStackRegisterRelation_executeAddi
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (immediate : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers sourceRegister + immediate))
      (execute target (.addi ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ immediate)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers sourceRegister + immediate))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨sourceRegister, hsource⟩ + immediate))
  rw [hsourceValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers sourceRegister + immediate)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeAdd
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left + source.registers right))
      (execute target (.add ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left + source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ + target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left + source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeSub
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left - source.registers right))
      (execute target (.sub ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left - source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ - target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left - source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeAnd
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left &&& source.registers right))
      (execute target (.and ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left &&& source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ &&& target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left &&& source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeOr
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left ||| source.registers right))
      (execute target (.or ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left ||| source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ ||| target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left ||| source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeXor
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left ^^^ source.registers right))
      (execute target (.xor ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left ^^^ source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ ^^^ target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left ^^^ source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeSll
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsl (source.registers left)
          (source.registers right)))
      (execute target (.sll ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.shiftLeft (source.registers left)
        (shiftAmount (source.registers right))))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.shiftLeft (target.registers ⟨left, hleft⟩)
        (shiftAmount (target.registers ⟨right, hright⟩))))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.shiftLeft (source.registers left)
      (shiftAmount (source.registers right)))
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeSrl
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsr (source.registers left)
          (source.registers right)))
      (execute target (.srl ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.ushiftRight (source.registers left)
        (shiftAmount (source.registers right))))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.ushiftRight (target.registers ⟨left, hleft⟩)
        (shiftAmount (target.registers ⟨right, hright⟩))))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.ushiftRight (source.registers left)
      (shiftAmount (source.registers right)))
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeSra
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .asr (source.registers left)
          (source.registers right)))
      (execute target (.sra ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.sshiftRight (source.registers left)
        (shiftAmount (source.registers right))))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (BitVec.sshiftRight (target.registers ⟨left, hleft⟩)
        (shiftAmount (target.registers ⟨right, hright⟩))))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (BitVec.sshiftRight (source.registers left)
      (shiftAmount (source.registers right)))
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeRor
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelationExceptX31 source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (hzero : source.registers 0 = 0)
    (hwidth : width = 32 ∨ width = 64)
    (hdestinationScratch : destination ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .ror (source.registers left)
          (source.registers right)))
      (executeInstructions target
        [.ori 31 0 (BitVec.ofNat width width),
         .sub 31 31 ⟨right, hright⟩,
         .sll 31 ⟨left, hleft⟩ 31,
         .srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
         .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]) := by
  have hleftValue := hrel left hleft hleftScratch
  have hrightValue := hrel right hright hrightScratch
  have hzeroValue := hrel 0 (by omega) (by omega)
  have hzeroValue' : target.registers 0 = 0 := by
    calc
      target.registers 0 = source.registers 0 := hzeroValue
      _ = 0 := hzero
  have hdestinationFinNonzero :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  have hdestinationFinScratch :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hdestinationScratch
    exact congrArg Fin.val heq
  have hleftFinScratch :
      (⟨left, hleft⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hleftScratch
    exact congrArg Fin.val heq
  have hrightFinScratch :
      (⟨right, hright⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hrightScratch
    exact congrArg Fin.val heq
  have hshift :
      shiftAmount (BitVec.ofNat width width - source.registers right) =
        (width - shiftAmount (source.registers right)) % width := by
    rcases hwidth with rfl | rfl <;>
      simp [shiftAmount, BitVec.toNat_sub] <;> omega
  have htargetDestination :
      (executeInstructions target
        [.ori 31 0 (BitVec.ofNat width width),
         .sub 31 31 ⟨right, hright⟩,
         .sll 31 ⟨left, hleft⟩ 31,
         .srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
         .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
          ⟨destination, hdestination⟩ =
      wordStackMachineShift .ror (source.registers left)
          (source.registers right) := by
    simp [executeInstructions, execute, readRegister, writeRegister,
      wordStackMachineShift, wordStackMachineRotateRight, hzeroValue',
      hleftValue, hrightValue, hleftFinScratch,
      hrightFinScratch, hdestinationFinNonzero, Ne.symm hdestinationFinScratch,
      ]
    rw [hshift]
    rfl
  intro register hregister hregisterScratch
  have htarget := hrel register hregister hregisterScratch
  by_cases hsame : register = destination
  · subst register
    simpa [wordStackMachineWriteRegister] using htargetDestination
  · have hfin : (⟨register, hregister⟩ : Fin 32) ≠
        ⟨destination, hdestination⟩ := by
      intro heq
      apply hsame
      exact congrArg Fin.val heq
    have hregisterFinScratch :
        (⟨register, hregister⟩ : Fin 32) ≠ 31 := by
      intro heq
      apply hregisterScratch
      exact congrArg Fin.val heq
    have htargetPreserved :
        (executeInstructions target
          [.ori 31 0 (BitVec.ofNat width width),
           .sub 31 31 ⟨right, hright⟩,
           .sll 31 ⟨left, hleft⟩ 31,
           .srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
           .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
            ⟨register, hregister⟩ = target.registers ⟨register, hregister⟩ := by
      simp [executeInstructions, execute, writeRegister, hfin,
        hregisterFinScratch, hdestinationFinNonzero]
    calc
      (executeInstructions target
          [.ori 31 0 (BitVec.ofNat width width),
           .sub 31 31 ⟨right, hright⟩,
           .sll 31 ⟨left, hleft⟩ 31,
           .srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
           .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
            ⟨register, hregister⟩ = target.registers ⟨register, hregister⟩ := htargetPreserved
      _ = source.registers register := htarget
      _ = (wordStackMachineWriteRegister source destination
          (wordStackMachineShift .ror (source.registers left)
            (source.registers right))).registers register := by
        simp [wordStackMachineWriteRegister, hsame]

theorem labCompilePlain_const
    [NeZero width] (destination value : Nat) (hdestination : destination < 32) :
    labCompilePlain (.const destination value : LabPlain (Word width)) =
      some [.addi ⟨destination, hdestination⟩ 0 (BitVec.ofNat width value)] := by
  simp [labCompilePlain, registerOfNat, hdestination]

theorem wordStackRegisterRelation_executeTick
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation source
      (execute target (.addi 0 0 (0 : Word width))) := by
  intro register hregister
  have htarget := hrel register hregister
  simp [execute, writeRegister, htarget]

theorem labCompilePlain_tick_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : labCompilePlain (.tick : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation source (executeInstructions target code) := by
  have hshape : labCompilePlain (.tick : LabPlain (Word width)) =
      some [.addi 0 0 (0 : Word width)] := by
    simp [labCompilePlain]
  rw [hshape] at hcode
  cases hcode
  simpa only [executeInstructions_single] using
    wordStackRegisterRelation_executeTick source target hrel

theorem evalWordStackMachine_tick [NeZero width]
    (state : WordStackMachineState width) :
    evalWordStackMachine state (.tick : StackProg Nat) = some state := by
  rfl

theorem compileStackProgramNatToRiscV_tick [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.tick : StackProg Nat) = some [.addi 0 0 (0 : Word width)] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel]

theorem compileStackProgramNatToRiscV_tick_register_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (source : WordStackMachineState width)
    (target : State width) (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV context config sectionId initialLabel
      (.tick : StackProg Nat) = some code) :
    WordStackRegisterRelation source (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_tick] at hcode
  cases hcode
  simpa only [executeInstructions_single] using
    wordStackRegisterRelation_executeTick source target hrel

theorem compileStackProgramNatToRiscV_const [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination value : Nat)
    (hdestination : destination < 32) :
    compileStackProgramNatToRiscV context config sectionId initialLabel
      (.const destination value : StackProg Nat) =
      some [.addi ⟨destination, hdestination⟩ 0 (BitVec.ofNat width value)] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, registerOfNat, hdestination,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel]

theorem compileStackProgramNatToRiscV_const_register_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination value : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdestinationNonzero : destination ≠ 0)
    (hzero : source.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV context config sectionId initialLabel
      (.const destination value : StackProg Nat) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (BitVec.ofNat width value))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_const context config sectionId initialLabel
    destination value hdestination] at hcode
  cases hcode
  have hsimulation := wordStackRegisterRelation_executeAddi source target
    destination 0 (BitVec.ofNat width value) hrel hdestination (by omega)
    hdestinationNonzero
  have hzeroAdd : source.registers 0 + BitVec.ofNat width value =
      BitVec.ofNat width value := by
    simpa using congrArg (fun register : Word width =>
      register + BitVec.ofNat width value) hzero
  rw [hzeroAdd] at hsimulation
  simpa [Fin.ext_iff] using hsimulation

theorem compileStackProgramNatToRiscV_add [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.arith .add destination left right : StackProg Nat) =
      some [.add ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labBinOpInstruction,
    labCollectLabels, labLineInstructionCount,
    registerOfNat, hdestination, hleft, hright,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel]
  congr 1

theorem compileStackProgramNatToRiscV_add_register_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination left right : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.arith .add destination left right : StackProg Nat) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left + source.registers right))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_add context config sectionId initialLabel
    destination left right hdestination hleft hright] at hcode
  cases hcode
  simpa [Fin.ext_iff] using
    (wordStackRegisterRelation_executeAdd source target destination left right
      hrel hdestination hleft hright hdestinationNonzero)

theorem labCompilePlain_const_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination value : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdestinationNonzero : destination ≠ 0)
    (hzero : source.registers 0 = 0) :
    (labCompilePlain (.const destination value : LabPlain (Word width))).bind
        (fun code =>
          some (WordStackRegisterRelation
            (wordStackMachineWriteRegister source destination
              (BitVec.ofNat width value))
            (executeInstructions target code))) =
      some (WordStackRegisterRelation
        (wordStackMachineWriteRegister source destination
          (BitVec.ofNat width value))
        (execute target (.addi ⟨destination, hdestination⟩ 0
          (BitVec.ofNat width value)))) := by
  rw [labCompilePlain_const destination value hdestination]
  change some (WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.ofNat width value))
    (execute target (.addi ⟨destination, hdestination⟩ 0
      (BitVec.ofNat width value)))) = _
  have hsimulation := wordStackRegisterRelation_executeAddi source target
    destination 0 (BitVec.ofNat width value) hrel hdestination (by omega)
    hdestinationNonzero
  have hzeroAdd : source.registers 0 + BitVec.ofNat width value =
      BitVec.ofNat width value := by
    simpa using congrArg (fun register : Word width =>
      register + BitVec.ofNat width value) hzero
  rw [hzeroAdd] at hsimulation

theorem labCompilePlain_add
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .add destination left right : LabPlain (Word width)) =
      some [.add ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_add_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .add destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left + source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_add (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left + source.registers right))
    (execute target (.add ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeAdd source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_sub
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .sub destination left right : LabPlain (Word width)) =
      some [.sub ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_sub_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .sub destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left - source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_sub (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left - source.registers right))
    (execute target (.sub ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeSub source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_and
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .and destination left right : LabPlain (Word width)) =
      some [.and ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_or
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .or destination left right : LabPlain (Word width)) =
      some [.or ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_xor
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .xor destination left right : LabPlain (Word width)) =
      some [.xor ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_and_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .and destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left &&& source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_and (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left &&& source.registers right))
    (execute target (.and ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeAnd source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_or_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .or destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left ||| source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_or (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left ||| source.registers right))
    (execute target (.or ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeOr source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_xor_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .xor destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left ^^^ source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_xor (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left ^^^ source.registers right))
    (execute target (.xor ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeXor source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_shift_lsl
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.shift .lsl destination left right : LabPlain (Word width)) =
      some [.sll ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labShiftInstructions, registerOfNat,
    hdestination, hleft, hright]

theorem labCompilePlain_shift_lsr
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.shift .lsr destination left right : LabPlain (Word width)) =
      some [.srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labShiftInstructions, registerOfNat,
    hdestination, hleft, hright]

theorem labCompilePlain_shift_asr
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.shift .asr destination left right : LabPlain (Word width)) =
      some [.sra ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labShiftInstructions, registerOfNat,
    hdestination, hleft, hright]

theorem labCompilePlain_shift_lsl_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.shift .lsl destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsl (source.registers left)
          (source.registers right)))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_shift_lsl (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (wordStackMachineShift .lsl (source.registers left)
        (source.registers right)))
    (execute target (.sll ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeSll source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_shift_lsr_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.shift .lsr destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .lsr (source.registers left)
          (source.registers right)))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_shift_lsr (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (wordStackMachineShift .lsr (source.registers left)
        (source.registers right)))
    (execute target (.srl ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeSrl source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_shift_asr_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.shift .asr destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .asr (source.registers left)
          (source.registers right)))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_shift_asr (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (wordStackMachineShift .asr (source.registers left)
        (source.registers right)))
    (execute target (.sra ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeSra source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_shift_ror
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationScratch : destination ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    labCompilePlain (.shift .ror destination left right : LabPlain (Word width)) =
      some [.ori 31 0 (BitVec.ofNat width width),
        .sub 31 31 ⟨right, hright⟩,
        .sll 31 ⟨left, hleft⟩ 31,
        .srl ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
        .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31] := by
  simp [labCompilePlain, labShiftInstructions, registerOfNat,
    hdestination, hleft, hright, hdestinationScratch, hleftScratch,
    hrightScratch]

theorem labCompilePlain_shift_ror_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelationExceptX31 source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (hzero : source.registers 0 = 0)
    (hwidth : width = 32 ∨ width = 64)
    (hdestinationScratch : destination ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.shift .ror destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .ror (source.registers left)
          (source.registers right)))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_shift_ror (width := width) destination left right
    hdestination hleft hright hdestinationScratch hleftScratch hrightScratch
  rw [hshape] at hcode
  cases hcode
  exact wordStackRegisterRelation_executeRor source target destination left right
    hrel hdestination hleft hright hdestinationNonzero hzero hwidth
    hdestinationScratch hleftScratch hrightScratch

end Flapjack.RiscV
