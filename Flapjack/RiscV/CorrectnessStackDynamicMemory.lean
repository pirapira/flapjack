import Flapjack.RiscV.CorrectnessStackMemory

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

end Flapjack.RiscV
