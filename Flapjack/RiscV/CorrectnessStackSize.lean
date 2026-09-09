import Flapjack.RiscV.CorrectnessStackDynamicStore

/-!
# StackRemove frame-size arithmetic at the RISC-V boundary

The frame-size query subtracts the configured frame base from the current
stack pointer and shifts the result by the machine word shift. The two code
shapes below account for the optimized move when the destination is already
the stack-pointer register.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveStackGetSize [NeZero width]
    (config : StackRemoveConfig) (target : State width) (register : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hstackBase : config.stackBase < 32)
    (hscratch : config.scratch < 32)
    (hregister : register < 32)
    (hregisterNonzero : register ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hregisterScratch : register ≠ config.scratch)
    (hregisterBase : register ≠ config.stackBase)
    (hzero : target.registers 0 = 0) :
    let code : List (Instruction width) :=
      if register = config.stackPointer then
        [.sub ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.stackBase, hstackBase⟩,
         .ori ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .srl ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩]
      else
        [.or ⟨register, hregister⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩,
         .sub ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.stackBase, hstackBase⟩,
         .ori ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .srl ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩]
    (executeInstructions target code).registers
        ⟨register, hregister⟩ =
      BitVec.ushiftRight
        (target.registers ⟨config.stackPointer, hstackPointer⟩ -
          target.registers ⟨config.stackBase, hstackBase⟩)
        (shiftAmount (BitVec.ofNat width config.wordShift)) := by
  have hregisterFinScratch :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.scratch, hscratch⟩ := by
    intro heq
    apply hregisterScratch
    exact congrArg Fin.val heq
  have hregisterFinBase :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.stackBase, hstackBase⟩ := by
    intro heq
    apply hregisterBase
    exact congrArg Fin.val heq
  have hregisterFinNonzero :
      (⟨register, hregister⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hregisterNonzero
    exact congrArg Fin.val heq
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  by_cases hpointer : register = config.stackPointer
  · subst register
    have hproof : hregister = hstackPointer := Subsingleton.elim _ _
    cases hproof
    simp [executeInstructions, execute, writeRegister, readRegister,
      hscratchFinNonzero, hregisterFinNonzero, hstackPointerScratch,
      hregisterNonzero, hzero]
  · simp [executeInstructions, execute, writeRegister, readRegister,
      hpointer, hregisterFinScratch, hregisterFinNonzero,
      hscratchFinNonzero, hregisterNonzero, hzero,
      Ne.symm hregisterBase]

end Flapjack.RiscV
