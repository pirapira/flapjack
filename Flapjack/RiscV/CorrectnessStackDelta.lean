import Flapjack.RiscV.CorrectnessStackSetSize
import Flapjack.RiscV.CorrectnessStack

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

theorem compileStackProgramNatToRiscV_stackAlloc_small [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hwords : words ≤ 255) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackAlloc words : StackProg Nat) =
      some (if words = 0 then [] else
        [.addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width (config.bytesInWord * words)),
         .sub ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.scratch, hscratch⟩]) := by
  by_cases hwordsZero : words = 0
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines,
      labCollectLabels,
      hwordsZero, stackRemoveStackAlloc, stackRemoveStackDelta,
      stackRemoveComplete, stackProgDepth, stackRemoveFuel]
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines,
      labCompilePlain, labCollectLabels, labLineInstructionCount,
      labBinOpInstruction, labPlainNatToWord, registerOfNat,
      hwordsZero, hwords, hstackPointer, hscratch, stackRemoveStackAlloc,
      stackRemoveStackDelta,
      stackRemoveJoin,
      stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
      congr 1

theorem compileStackProgramNatToRiscV_stackFree_small [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hwords : words ≤ 255) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackFree words : StackProg Nat) =
      some (if words = 0 then [] else
        [.addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width (config.bytesInWord * words)),
         .add ⟨config.stackPointer, hstackPointer⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.scratch, hscratch⟩]) := by
  by_cases hwordsZero : words = 0
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines,
      labCollectLabels,
      hwordsZero, stackRemoveStackFree, stackRemoveStackDelta,
      stackRemoveComplete, stackProgDepth, stackRemoveFuel]
  · simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove,
      labProgramToSection, labSectionNatToWord, labLineNatToWord,
      labLabel, labIsSequence, labFlatten, labCompileLines,
      labCompilePlain, labCollectLabels, labLineInstructionCount,
      labBinOpInstruction, labPlainNatToWord, registerOfNat,
      hwordsZero, hwords, hstackPointer, hscratch, stackRemoveStackFree,
      stackRemoveStackDelta,
      stackRemoveJoin,
      stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
      congr 1

theorem compileStackProgramNatToRiscV_stackAlloc_small_value [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackAlloc words : StackProg Nat) = some code) :
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackPointer, hstackPointer⟩ -
        BitVec.ofNat width (config.bytesInWord * words) := by
  rw [compileStackProgramNatToRiscV_stackAlloc_small context config sectionId
    initialLabel words hstackPointer hscratch hwords] at hcode
  cases hcode
  exact executeStackRemoveStackAlloc_small config target words hstackPointer hscratch
    hstackPointerNonzero hscratchNonzero hscratchPointer hwords hzero

theorem compileStackProgramNatToRiscV_stackFree_small_value [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackFree words : StackProg Nat) = some code) :
    (executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩ =
      target.registers ⟨config.stackPointer, hstackPointer⟩ +
        BitVec.ofNat width (config.bytesInWord * words) := by
  rw [compileStackProgramNatToRiscV_stackFree_small context config sectionId
    initialLabel words hstackPointer hscratch hwords] at hcode
  cases hcode
  exact executeStackRemoveStackFree_small config target words hstackPointer hscratch
    hstackPointerNonzero hscratchNonzero hscratchPointer hwords hzero

theorem compileStackProgramNatToRiscV_stackAlloc_small_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackAlloc words : StackProg Nat) = some code) :
    (evalWordStackMachine source
      (stackRemoveStackAlloc config words)).map
        (fun final => final.registers config.stackPointer) =
      some ((executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩) := by
  have hsourcePointer := hrel config.stackPointer hstackPointer
    hscratchPointer.symm
  rw [evalStackRemoveStackAlloc_small config source words hwords hscratchPointer]
  congr 1
  have hvalue := compileStackProgramNatToRiscV_stackAlloc_small_value
    context config sectionId initialLabel words target hstackPointer hscratch
    hstackPointerNonzero hscratchNonzero hscratchPointer hwords hzero code hcode
  rw [hvalue]
  simp [hsourcePointer]

theorem compileStackProgramNatToRiscV_stackFree_small_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel words : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (hscratch : config.scratch < 32)
    (hstackPointerNonzero : config.stackPointer ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (hscratchPointer : config.scratch ≠ config.stackPointer)
    (hwords : words ≤ 255)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackFree words : StackProg Nat) = some code) :
    (evalWordStackMachine source
      (stackRemoveStackFree config words)).map
        (fun final => final.registers config.stackPointer) =
      some ((executeInstructions target code).registers
        ⟨config.stackPointer, hstackPointer⟩) := by
  have hsourcePointer := hrel config.stackPointer hstackPointer
    hscratchPointer.symm
  rw [evalStackRemoveStackFree_small config source words hwords hscratchPointer]
  congr 1
  have hvalue := compileStackProgramNatToRiscV_stackFree_small_value
    context config sectionId initialLabel words target hstackPointer hscratch
    hstackPointerNonzero hscratchNonzero hscratchPointer hwords hzero code hcode
  rw [hvalue]
  simp [hsourcePointer]

end Flapjack.RiscV
