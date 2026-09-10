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

theorem compileStackProgramNatToRiscV_stackSetSize [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hstackBase : config.stackBase < 32)
    (hscratch : config.scratch < 32)
    (haddressScratch : config.addressScratch < 32)
    (hregister : register < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackSetSize register : StackProg Nat) =
      some (if register = config.scratch then
        [.addi ⟨config.addressScratch, haddressScratch⟩ 0
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
        [.addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .sll ⟨register, hregister⟩ ⟨register, hregister⟩
           ⟨config.scratch, hscratch⟩,
         .or ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackBase, hstackBase⟩
           ⟨config.stackBase, hstackBase⟩,
         .add ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨register, hregister⟩]) := by
  by_cases hregisterScratch : register = config.scratch
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines, labCompilePlain,
      labCollectLabels, labLineInstructionCount, labBinOpInstruction,
      labPlainNatToWord, registerOfNat, labShiftInstructions,
      hregisterScratch, hstackPointer, hstackBase, hscratch, haddressScratch,
      stackRemoveStackSetSize,
      stackRemoveJoin, stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
      congr 1
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines, labCompilePlain,
      labCollectLabels, labLineInstructionCount, labBinOpInstruction,
      labPlainNatToWord, registerOfNat, labShiftInstructions,
      hregisterScratch, hstackPointer, hstackBase, hscratch,
      hregister, stackRemoveStackSetSize,
      stackRemoveJoin, stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
      congr 1

theorem compileStackProgramNatToRiscV_stackSetSize_value [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register : Nat) (target : State width)
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
    (hzero : target.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackSetSize register : StackProg Nat) = some code) :
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackBase, hstackBase⟩ +
        BitVec.shiftLeft (target.registers ⟨register, hregister⟩)
          (shiftAmount (BitVec.ofNat width config.wordShift)) := by
  rw [compileStackProgramNatToRiscV_stackSetSize context config sectionId initialLabel
    register hstackPointer hstackBase hscratch haddressScratch hregister] at hcode
  cases hcode
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
  by_cases hregisterScratch' : register = config.scratch
  · have haddiOri :
        executeInstructions target
            [.addi ⟨config.addressScratch, haddressScratch⟩ 0
              (BitVec.ofNat width config.wordShift),
             .sll ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.addressScratch, haddressScratch⟩,
             .or ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackBase, hstackBase⟩
               ⟨config.stackBase, hstackBase⟩,
             .add ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackPointer, hstackPointer⟩
               ⟨register, hregister⟩] =
        executeInstructions target
            [.ori ⟨config.addressScratch, haddressScratch⟩ 0
              (BitVec.ofNat width config.wordShift),
             .sll ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.addressScratch, haddressScratch⟩,
             .or ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackBase, hstackBase⟩
               ⟨config.stackBase, hstackBase⟩,
             .add ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackPointer, hstackPointer⟩
               ⟨register, hregister⟩] := by
      simp only [executeInstructions]
      rw [execute_addi_zero_eq_execute_ori_zero target
        ⟨config.addressScratch, haddressScratch⟩
        (BitVec.ofNat width config.wordShift)
        haddressScratchFinNonzero hzero]
    simp only [if_pos hregisterScratch']
    rw [haddiOri]
    simpa [hregisterScratch'] using
      executeStackRemoveStackSetSize config target register hstackPointer hstackBase
        hscratch haddressScratch hregister hstackPointerNonzero hstackBaseNonzero
        hscratchNonzero haddressScratchNonzero hregisterNonzero hregisterBase
        hregisterPointer hbaseScratch hbaseAddress hscratchAddress hzero
  · have haddiOri :
        executeInstructions target
            [.addi ⟨config.scratch, hscratch⟩ 0
              (BitVec.ofNat width config.wordShift),
             .sll ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.scratch, hscratch⟩,
             .or ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackBase, hstackBase⟩
               ⟨config.stackBase, hstackBase⟩,
             .add ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackPointer, hstackPointer⟩
               ⟨register, hregister⟩] =
        executeInstructions target
            [.ori ⟨config.scratch, hscratch⟩ 0
              (BitVec.ofNat width config.wordShift),
             .sll ⟨register, hregister⟩ ⟨register, hregister⟩
               ⟨config.scratch, hscratch⟩,
             .or ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackBase, hstackBase⟩
               ⟨config.stackBase, hstackBase⟩,
             .add ⟨config.stackPointer, hstackPointer⟩
               ⟨config.stackPointer, hstackPointer⟩
               ⟨register, hregister⟩] := by
      simp only [executeInstructions]
      rw [execute_addi_zero_eq_execute_ori_zero target
        ⟨config.scratch, hscratch⟩
        (BitVec.ofNat width config.wordShift)
        hscratchFinNonzero hzero]
    simp only [if_neg hregisterScratch']
    rw [haddiOri]
    simpa [hregisterScratch'] using
      executeStackRemoveStackSetSize config target register hstackPointer hstackBase
        hscratch haddressScratch hregister hstackPointerNonzero hstackBaseNonzero
        hscratchNonzero haddressScratchNonzero hregisterNonzero hregisterBase
        hregisterPointer hbaseScratch hbaseAddress hscratchAddress hzero

theorem compileStackProgramNatToRiscV_stackSetSize_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register : Nat)
    (source : WordStackMachineState width) (target : State width)
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
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddress : config.stackPointer ≠ config.addressScratch)
    (hregisterBase : register ≠ config.stackBase)
    (hregisterPointer : register ≠ config.stackPointer)
    (hbaseScratch : config.stackBase ≠ config.scratch)
    (hbaseAddress : config.stackBase ≠ config.addressScratch)
    (hscratchAddress : config.scratch ≠ config.addressScratch)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackSetSize register : StackProg Nat) = some code) :
    (evalWordStackMachine source
      (stackRemoveStackSetSize config register)).map
        (fun final => final.registers config.stackPointer) =
      some ((executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩) := by
  have hsourceBase := hrel config.stackBase hstackBase
  have hsourceRegister := hrel register hregister
  rw [evalStackRemoveStackSetSize config source register hscratchAddress
    hstackPointerScratch hstackPointerAddress hregisterBase hregisterPointer
    hbaseScratch hbaseAddress]
  congr 1
  have hvalue := compileStackProgramNatToRiscV_stackSetSize_value
    context config sectionId initialLabel register target hstackPointer hstackBase
    hscratch haddressScratch hregister hstackPointerNonzero hstackBaseNonzero
    hscratchNonzero haddressScratchNonzero hregisterNonzero hregisterBase
    hregisterPointer hbaseScratch hbaseAddress hscratchAddress hzero code hcode
  rw [hvalue]
  simp [hsourceBase, hsourceRegister]

end Flapjack.RiscV
