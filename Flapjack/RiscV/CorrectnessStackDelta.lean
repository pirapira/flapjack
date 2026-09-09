import Flapjack.RiscV.CorrectnessStackSetSize

/-!
# StackRemove frame allocation and release at the RISC-V boundary

For a non-zero delta of at most 255 words, StackRemove materializes the byte
count in the configured scratch register and updates the stack pointer.  The
zero-word case is the empty program.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveStackAlloc_small [NeZero width]
    (config : StackRemoveConfig) (target : State width) (words : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0) :
    let code : List (Instruction width) :=
      if words = 0 then
        []
      else
        [.addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width (config.bytesInWord * words)),
         .sub ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.scratch, hscratch⟩]
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackPointer, hstackPointer⟩ -
        BitVec.ofNat width (config.bytesInWord * words) := by
  have hstackPointerFinNonzero :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hstackPointerNonzero
    exact congrArg Fin.val heq
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  have hscratchFinPointer :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠
        ⟨config.stackPointer, hstackPointer⟩ := by
    intro heq
    apply hscratchPointer
    exact congrArg Fin.val heq
  by_cases hwordsZero : words = 0
  · subst words
    simp [executeInstructions]
  · simp [executeInstructions, execute, writeRegister, readRegister,
      hwordsZero, hstackPointerFinNonzero, hscratchFinNonzero,
      Ne.symm hscratchPointer, hzero]

theorem executeStackRemoveStackFree_small [NeZero width]
    (config : StackRemoveConfig) (target : State width) (words : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0) :
    let code : List (Instruction width) :=
      if words = 0 then
        []
      else
        [.addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width (config.bytesInWord * words)),
         .add ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.scratch, hscratch⟩]
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackPointer, hstackPointer⟩ +
        BitVec.ofNat width (config.bytesInWord * words) := by
  have hstackPointerFinNonzero :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hstackPointerNonzero
    exact congrArg Fin.val heq
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  have hscratchFinPointer :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠
        ⟨config.stackPointer, hstackPointer⟩ := by
    intro heq
    apply hscratchPointer
    exact congrArg Fin.val heq
  by_cases hwordsZero : words = 0
  · subst words
    simp [executeInstructions]
  · simp [executeInstructions, execute, writeRegister, readRegister,
      hwordsZero, hstackPointerFinNonzero, hscratchFinNonzero,
      Ne.symm hscratchPointer, hzero]

end Flapjack.RiscV
