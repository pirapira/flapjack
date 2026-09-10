import Flapjack.RiscV.CorrectnessStackDynamicStore

/-!
# StackRemove frame-size arithmetic at the RISC-V boundary

The frame-size query subtracts the configured frame base from the current
stack pointer and shifts the result by the machine word shift. The two code
shapes below account for the optimized move when the destination is already
the stack-pointer register.
-/

namespace Flapjack.RiscV

theorem execute_addi_zero_eq_execute_ori_zero [NeZero width]
    (state : State width) (register : Fin 32) (value : Word width)
    (hregister : register ≠ 0) (hzero : state.registers 0 = 0) :
    execute state (.addi register 0 value) =
      execute state (.ori register 0 value) := by
  simp [execute, writeRegister, readRegister, hregister, hzero]

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

theorem compileStackProgramNatToRiscV_stackGetSize [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hstackBase : config.stackBase < 32)
    (hscratch : config.scratch < 32)
    (hregister : register < 32)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hregisterScratch : register ≠ config.scratch) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackGetSize register : StackProg Nat) =
      some (if register = config.stackPointer then
        [.sub ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.stackBase, hstackBase⟩,
         .addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .srl ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩]
      else
        [.or ⟨register, hregister⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩,
         .sub ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.stackBase, hstackBase⟩,
         .addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .srl ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩]) := by
  by_cases hpointer : register = config.stackPointer
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines, labCompilePlain,
      labCollectLabels, labLineInstructionCount, labBinOpInstruction,
      labPlainNatToWord, registerOfNat, labShiftInstructions,
      hpointer, hstackPointer, hstackBase, hscratch,
      hstackPointerScratch, stackRemoveStackGetSize,
      stackRemoveMove, stackRemoveJoin, stackRemoveComplete, stackProgDepth,
      stackRemoveFuel] <;>
      congr 1
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines, labCompilePlain,
      labCollectLabels, labLineInstructionCount, labBinOpInstruction,
      labPlainNatToWord, registerOfNat, labShiftInstructions,
      hpointer, hstackPointer, hstackBase, hscratch, hregister,
      hregisterScratch,
      stackRemoveStackGetSize,
      stackRemoveMove, stackRemoveJoin, stackRemoveComplete, stackProgDepth,
      stackRemoveFuel] <;>
      congr 1

theorem compileStackProgramNatToRiscV_stackGetSize_value [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register : Nat) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (hstackBase : config.stackBase < 32)
    (hscratch : config.scratch < 32)
    (hregister : register < 32)
    (hregisterNonzero : register ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hregisterScratch : register ≠ config.scratch)
    (hregisterBase : register ≠ config.stackBase)
    (hzero : target.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackGetSize register : StackProg Nat) = some code) :
    (executeInstructions target code).registers ⟨register, hregister⟩ =
      BitVec.ushiftRight
        (target.registers ⟨config.stackPointer, hstackPointer⟩ -
          target.registers ⟨config.stackBase, hstackBase⟩)
        (shiftAmount (BitVec.ofNat width config.wordShift)) := by
  rw [compileStackProgramNatToRiscV_stackGetSize context config sectionId initialLabel
    register hstackPointer hstackBase hscratch hregister hstackPointerScratch
    hregisterScratch] at hcode
  cases hcode
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  have haddiOri :
      executeInstructions target
          (if register = config.stackPointer then
            [.sub ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.stackBase, hstackBase⟩,
             .addi ⟨config.scratch, hscratch⟩ 0
               (BitVec.ofNat width config.wordShift),
             .srl ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.scratch, hscratch⟩]
          else
            [.or ⟨register, hregister⟩
               ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackPointer, hstackPointer⟩,
             .sub ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.stackBase, hstackBase⟩,
             .addi ⟨config.scratch, hscratch⟩ 0
               (BitVec.ofNat width config.wordShift),
             .srl ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.scratch, hscratch⟩]) =
        executeInstructions target
          (if register = config.stackPointer then
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
               ⟨config.scratch, hscratch⟩]) := by
    by_cases hpointer : register = config.stackPointer
    · subst register
      have hsubzero :
          (execute target
            (.sub ⟨config.stackPointer, hregister⟩
              ⟨config.stackPointer, hregister⟩
              ⟨config.stackBase, hstackBase⟩)).registers 0 = 0 := by
        simp [execute, writeRegister, readRegister, hregisterNonzero, hzero]
      simp only [if_true, executeInstructions]
      rw [execute_addi_zero_eq_execute_ori_zero
        (execute target (.sub ⟨config.stackPointer, hregister⟩
          ⟨config.stackPointer, hregister⟩ ⟨config.stackBase, hstackBase⟩))
        ⟨config.scratch, hscratch⟩ (BitVec.ofNat width config.wordShift)
        hscratchFinNonzero hsubzero]
    · have hsubzero :
          (execute (execute target
            (.or ⟨register, hregister⟩
              ⟨config.stackPointer, hstackPointer⟩
              ⟨config.stackPointer, hstackPointer⟩))
            (.sub ⟨register, hregister⟩ ⟨register, hregister⟩
              ⟨config.stackBase, hstackBase⟩)).registers 0 = 0 := by
        simp [execute, writeRegister, readRegister, hregisterNonzero, hzero]
      simp only [if_neg hpointer, executeInstructions]
      rw [execute_addi_zero_eq_execute_ori_zero
        (execute (execute target
          (.or ⟨register, hregister⟩
            ⟨config.stackPointer, hstackPointer⟩
            ⟨config.stackPointer, hstackPointer⟩))
          (.sub ⟨register, hregister⟩ ⟨register, hregister⟩
            ⟨config.stackBase, hstackBase⟩))
        ⟨config.scratch, hscratch⟩ (BitVec.ofNat width config.wordShift)
        hscratchFinNonzero hsubzero]
  rw [haddiOri]
  exact executeStackRemoveStackGetSize config target register hstackPointer hstackBase
    hscratch hregister hregisterNonzero hscratchNonzero hstackPointerScratch
    hregisterScratch hregisterBase hzero

end Flapjack.RiscV
