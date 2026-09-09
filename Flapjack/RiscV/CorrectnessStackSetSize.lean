import Flapjack.RiscV.CorrectnessStackSize

/-!
# StackRemove frame-size updates at the RISC-V boundary

The frame-size setter shifts a register-held size, restores the configured
frame base into the stack pointer, and adds the shifted size.  The shift
scratch changes when the size register is itself the normal scratch register.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveStackSetSize [NeZero width]
    (config : StackRemoveConfig) (target : State width) (register : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hstackBase : config.stackBase < 32)
    (hscratch : config.scratch < 32)
    (haddressScratch : config.addressScratch < 32)
    (hregister : register < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hstackBaseNonzero : config.stackBase ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hregisterNonzero : register ≠ 0)
    (hregisterBase : register ≠ config.stackBase)
    (hregisterPointer : register ≠ config.stackPointer)
    (hbaseScratch : config.stackBase ≠ config.scratch)
    (hbaseAddress : config.stackBase ≠ config.addressScratch)
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hzero : target.registers 0 = 0) :
    let code : List (Instruction width) :=
      if register = config.scratch then
        [.ori ⟨config.addressScratch, haddressScratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .sll ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.addressScratch, haddressScratch⟩,
         .or ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackBase, hstackBase⟩
           ⟨config.stackBase, hstackBase⟩,
         .add ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨register, hregister⟩]
      else
        [.ori ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .sll ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩,
         .or ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackBase, hstackBase⟩
           ⟨config.stackBase, hstackBase⟩,
         .add ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨register, hregister⟩]
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackBase, hstackBase⟩ +
        BitVec.shiftLeft (target.registers ⟨register, hregister⟩)
          (shiftAmount (BitVec.ofNat width config.wordShift)) := by
  have hstackPointerFinNonzero :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hstackPointerNonzero
    exact congrArg Fin.val heq
  have hstackBaseFinNonzero :
      (⟨config.stackBase, hstackBase⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hstackBaseNonzero
    exact congrArg Fin.val heq
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  have haddressScratchFinNonzero :
      (⟨config.addressScratch, haddressScratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply haddressScratchNonzero
    exact congrArg Fin.val heq
  have hregisterFinNonzero :
      (⟨register, hregister⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hregisterNonzero
    exact congrArg Fin.val heq
  have hregisterFinBase :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.stackBase, hstackBase⟩ := by
    intro heq
    apply hregisterBase
    exact congrArg Fin.val heq
  have hregisterFinPointer :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.stackPointer, hstackPointer⟩ := by
    intro heq
    apply hregisterPointer
    exact congrArg Fin.val heq
  have hbaseFinScratch :
      (⟨config.stackBase, hstackBase⟩ : Fin 32) ≠
        ⟨config.scratch, hscratch⟩ := by
    intro heq
    apply hbaseScratch
    exact congrArg Fin.val heq
  have hbaseFinAddress :
      (⟨config.stackBase, hstackBase⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hbaseAddress
    exact congrArg Fin.val heq
  have hscratchFinAddress :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hscratchAddress
    exact congrArg Fin.val heq
  by_cases hregisterScratch' : register = config.scratch
  · subst register
    have hproof : hregister = hscratch := Subsingleton.elim _ _
    cases hproof
    simp [executeInstructions, execute, writeRegister, readRegister,
      hstackPointerFinNonzero, hscratchFinNonzero,
      haddressScratchFinNonzero, hbaseFinAddress,
      hscratchFinAddress, hbaseScratch, hregisterPointer, hzero]
  · simp [executeInstructions, execute, writeRegister, readRegister,
      hregisterScratch', hregisterFinPointer,
      hstackPointerFinNonzero, hscratchFinNonzero,
      hregisterNonzero, hbaseScratch, Ne.symm hregisterBase, hzero]

end Flapjack.RiscV
