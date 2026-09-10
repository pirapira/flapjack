import Flapjack.RiscV.CorrectnessStackMemory
import Flapjack.RiscV.CorrectnessStackRemoveDynamic

/-!
# Dynamic StackRemove frame-cell loads at the RISC-V boundary

The dynamic stack load receives an already-computed byte offset in a register.
This file proves the corresponding two-instruction RISC-V sequence against the
abstract StackLang frame cell.
-/

namespace Flapjack.RiscV

theorem writeRegister_memory_dynamic (state : State width) (register : Fin 32)
    (value : Word width) :
    (writeRegister state register value).memory = state.memory := by
  unfold writeRegister
  split <;> rfl

theorem executeStackRemoveStackLoadAny [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (destination offsetRegister offset : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hrel : WordStackRegisterRelationExceptRegister config.addressScratch source target)
    (hcell :
      readWordValue target
          (target.registers ⟨config.stackPointer, hstackPointer⟩ +
            target.registers ⟨offsetRegister, hoffsetRegister⟩) =
        source.stack offset) :
    WordStackRegisterRelationExceptRegister config.addressScratch
      (wordStackMachineWriteRegister source destination (source.stack offset))
      (executeInstructions target
        [.add ⟨config.addressScratch, haddressScratch⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨offsetRegister, hoffsetRegister⟩,
         .loadWord ⟨destination, hdestination⟩
           ⟨config.addressScratch, haddressScratch⟩]) := by
  intro register hregister hregisterScratch
  have htarget := hrel register hregister hregisterScratch
  have hregisterFinScratch :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hregisterScratch
    exact congrArg Fin.val heq
  have haddressScratchFinNonzero :
      (⟨config.addressScratch, haddressScratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply haddressScratchNonzero
    exact congrArg Fin.val heq
  have hstackPointerFinAddressScratch :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hstackPointerAddressScratch
    exact congrArg Fin.val heq
  let afterAddress := execute target
    (.add ⟨config.addressScratch, haddressScratch⟩
      ⟨config.stackPointer, hstackPointer⟩
      ⟨offsetRegister, hoffsetRegister⟩)
  have hafterAddressScratch :
      afterAddress.registers ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    simp [afterAddress, execute, writeRegister, readRegister,
      haddressScratchFinNonzero]
  have hafterAddressMemory : afterAddress.memory = target.memory := by
    simpa [afterAddress, execute, readRegister] using
      writeRegister_memory_dynamic
        ({ target with pc := nextPc target })
        ⟨config.addressScratch, haddressScratch⟩
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)
  have hafterAddressRegister (reg : Fin 32)
      (hregScratch : reg ≠ ⟨config.addressScratch, haddressScratch⟩) :
      afterAddress.registers reg = target.registers reg := by
    simp [afterAddress, execute, writeRegister, readRegister,
      haddressScratchFinNonzero, hregScratch]
  have hreadAddress :
      readWordValue afterAddress
          (afterAddress.registers ⟨config.addressScratch, haddressScratch⟩) =
        readWordValue target
          (target.registers ⟨config.stackPointer, hstackPointer⟩ +
            target.registers ⟨offsetRegister, hoffsetRegister⟩) := by
    rw [hafterAddressScratch]
    simp [readWordValue, readByte, hafterAddressMemory]
  have hdestinationFinNonzero :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  by_cases hsame : register = destination
  · subst register
    have hproof : hregister = hdestination := Subsingleton.elim _ _
    cases hproof
    have hloadValue :
        (execute afterAddress
          (.loadWord ⟨destination, hdestination⟩
            ⟨config.addressScratch, haddressScratch⟩)).registers
              ⟨destination, hdestination⟩ =
          readWordValue target
            (target.registers ⟨config.stackPointer, hstackPointer⟩ +
              target.registers ⟨offsetRegister, hoffsetRegister⟩) := by
      simp only [execute, readRegister]
      rw [hreadAddress]
      simp [writeRegister, hdestinationFinNonzero]
    change (execute afterAddress
        (.loadWord ⟨destination, hdestination⟩
          ⟨config.addressScratch, haddressScratch⟩)).registers
            ⟨destination, hdestination⟩ =
      (wordStackMachineWriteRegister source destination
        (source.stack offset)).registers destination
    rw [hloadValue, hcell]
    simp [wordStackMachineWriteRegister]
  · have hregisterFinDestination :
        (⟨register, hregister⟩ : Fin 32) ≠
          ⟨destination, hdestination⟩ := by
      intro heq
      apply hsame
      exact congrArg Fin.val heq
    have hafterAddressRegister' :=
      hafterAddressRegister ⟨register, hregister⟩ hregisterFinScratch
    have hloadPreserved :
        (execute afterAddress
          (.loadWord ⟨destination, hdestination⟩
            ⟨config.addressScratch, haddressScratch⟩)).registers
              ⟨register, hregister⟩ = target.registers ⟨register, hregister⟩ := by
      simp [execute, writeRegister, readRegister, hafterAddressMemory,
        hafterAddressRegister', hregisterFinDestination, hdestinationNonzero]
    change (execute afterAddress
        (.loadWord ⟨destination, hdestination⟩
          ⟨config.addressScratch, haddressScratch⟩)).registers
            ⟨register, hregister⟩ =
      (wordStackMachineWriteRegister source destination
        (source.stack offset)).registers register
    rw [hloadPreserved]
    simp [wordStackMachineWriteRegister, htarget, hsame]

theorem compileStackProgramNatToRiscV_stackLoadAny [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination offsetRegister : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (hoffsetRegister : offsetRegister < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackLoadAny destination offsetRegister : StackProg Nat) =
      some [.add ⟨config.addressScratch, haddressScratch⟩
          ⟨config.stackPointer, hstackPointer⟩
          ⟨offsetRegister, hoffsetRegister⟩,
        .loadWord ⟨destination, hdestination⟩
          ⟨config.addressScratch, haddressScratch⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, labBinOpInstruction, wordInstToInstruction,
    registerOfNat, hstackPointer, haddressScratch, hdestination,
    hoffsetRegister, stackRemoveStackLoadAny, stackRemoveJoin,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_stackLoadAny_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination offsetRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hrel : WordStackRegisterRelationExceptRegister config.addressScratch source target)
    (offset : Nat)
    (hcell : readWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩) =
      source.stack offset)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackLoadAny destination offsetRegister : StackProg Nat) =
      some code) :
    WordStackRegisterRelationExceptRegister config.addressScratch
      (wordStackMachineWriteRegister source destination (source.stack offset))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_stackLoadAny context config sectionId initialLabel
    destination offsetRegister hstackPointer haddressScratch hdestination
    hoffsetRegister] at hcode
  cases hcode
  exact executeStackRemoveStackLoadAny config source target destination offsetRegister offset
    hstackPointer haddressScratch hoffsetRegister hdestination hdestinationNonzero
    haddressScratchNonzero hstackPointerAddressScratch hrel hcell

theorem compileStackProgramNatToRiscV_stackLoadAny_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination offsetRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (offset : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hdestinationScratch : destination ≠ config.addressScratch)
    (hrel : WordStackRegisterRelationExceptRegister config.addressScratch source target)
    (hmemory : source.memory
      (source.registers config.stackPointer + source.registers offsetRegister) =
      source.stack offset)
    (hcell : readWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩) =
      source.stack offset)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackLoadAny destination offsetRegister : StackProg Nat) =
      some code) :
    (evalWordStackMachine source
      (stackRemoveStackLoadAny config destination offsetRegister)).map
        (fun final => final.registers destination) =
      some ((executeInstructions target code).registers
        ⟨destination, hdestination⟩) := by
  rw [evalStackRemoveStackLoadAny config source destination offsetRegister, hmemory]
  congr 1
  have hsim := compileStackProgramNatToRiscV_stackLoadAny_simulation
    context config sectionId initialLabel destination offsetRegister source target
    hstackPointer haddressScratch hoffsetRegister hdestination hdestinationNonzero
    haddressScratchNonzero hstackPointerAddressScratch hrel offset hcell code hcode
  have hdest := hsim destination hdestination hdestinationScratch
  simpa [wordStackMachineWriteRegister] using hdest.symm

end Flapjack.RiscV
