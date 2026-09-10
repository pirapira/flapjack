import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# StackRemove frame-cell simulation at the RISC-V boundary

`StackRemove` represents a stack slot as one abstract word.  The RISC-V
backend represents the same slot by a little-endian architectural word at
`sp + bytesInWord * offset`.  This file records the first machine-level
contract for that boundary: the address-scratch sequence emitted for a
`stackLoad` produces the abstract slot value.

The register relation deliberately excludes the address scratch register.
StackRemove is allowed to clobber that temporary, while the logical
StackLang operation only changes its destination register.
-/

namespace Flapjack.RiscV

def WordStackRegisterRelationExceptRegister [NeZero width]
    (ignored : Nat) (source : WordStackMachineState width)
    (target : State width) : Prop :=
  ∀ register (hregister : register < 32), register ≠ ignored →
    target.registers ⟨register, hregister⟩ = source.registers register

def WordStackStackCellRelation [NeZero width]
    (source : WordStackMachineState width) (target : State width)
    (stackPointer : Fin 32) (bytesInWord offset : Nat) : Prop :=
  readWordValue target
      (target.registers stackPointer + BitVec.ofNat width (bytesInWord * offset)) =
    source.stack offset

theorem executeStackRemoveStackLoad [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (destination offset : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.addressScratch)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelationExceptRegister config.addressScratch source target)
    (hcell : WordStackStackCellRelation source target
      ⟨config.stackPointer, hstackPointer⟩ config.bytesInWord offset) :
    WordStackRegisterRelationExceptRegister config.addressScratch
      (wordStackMachineWriteRegister source destination (source.stack offset))
      (executeInstructions target
        [.addi ⟨config.addressScratch, haddressScratch⟩ 0
          (BitVec.ofNat width (config.bytesInWord * offset)),
         .add ⟨config.addressScratch, haddressScratch⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.addressScratch, haddressScratch⟩,
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
  let afterImmediate := execute target
    (.addi ⟨config.addressScratch, haddressScratch⟩ 0
      (BitVec.ofNat width (config.bytesInWord * offset)))
  let afterAddress := execute afterImmediate
    (.add ⟨config.addressScratch, haddressScratch⟩
      ⟨config.stackPointer, hstackPointer⟩
      ⟨config.addressScratch, haddressScratch⟩)
  have hstackPointerFinScratch :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hstackPointerScratch
    exact congrArg Fin.val heq
  have hafterImmediateRegister (reg : Fin 32)
      (hregScratch : reg ≠ ⟨config.addressScratch, haddressScratch⟩) :
      afterImmediate.registers reg = target.registers reg := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hregScratch]
  have hafterImmediateStackPointer :
      afterImmediate.registers ⟨config.stackPointer, hstackPointer⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ :=
    hafterImmediateRegister _ hstackPointerFinScratch
  have hafterImmediateScratch :
      afterImmediate.registers ⟨config.addressScratch, haddressScratch⟩ =
        BitVec.ofNat width (config.bytesInWord * offset) := by
    simp [afterImmediate, execute, writeRegister, readRegister, nextPc,
      haddressScratchNonzero, hzero]
  have hafterAddressScratch :
      afterAddress.registers ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          BitVec.ofNat width (config.bytesInWord * offset) := by
    simp [afterAddress, execute, writeRegister, readRegister, nextPc,
      hafterImmediateScratch, hafterImmediateStackPointer, haddressScratchNonzero]
  have hafterAddressMemory : afterAddress.memory = target.memory := by
    simp [afterAddress, afterImmediate, execute, writeRegister,
      haddressScratchNonzero]
  have hafterAddressRegister (reg : Fin 32)
      (hregScratch : reg ≠ ⟨config.addressScratch, haddressScratch⟩) :
      afterAddress.registers reg = target.registers reg := by
    simp [afterAddress, afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hregScratch]
  have hreadAddress :
      readWordValue afterAddress
          (afterAddress.registers ⟨config.addressScratch, haddressScratch⟩) =
        readWordValue target
          (target.registers ⟨config.stackPointer, hstackPointer⟩ +
            BitVec.ofNat width (config.bytesInWord * offset)) := by
    rw [hafterAddressScratch]
    simp [readWordValue, readByte, hafterAddressMemory]
  by_cases hsame : register = destination
  · subst register
    have hproof : hregister = hdestination := Subsingleton.elim _ _
    cases hproof
    have hdestinationFinNonzero :
        (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
      intro heq
      apply hdestinationNonzero
      exact congrArg Fin.val heq
    have hdestinationFinScratch :
        (⟨destination, hdestination⟩ : Fin 32) ≠
          ⟨config.addressScratch, haddressScratch⟩ := by
      intro heq
      apply hregisterScratch
      exact congrArg Fin.val heq
    have hloadValue :
        (execute afterAddress
          (.loadWord ⟨destination, hdestination⟩
            ⟨config.addressScratch, haddressScratch⟩)).registers
              ⟨destination, hdestination⟩ =
          readWordValue target
            (target.registers ⟨config.stackPointer, hstackPointer⟩ +
              BitVec.ofNat width (config.bytesInWord * offset)) := by
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
