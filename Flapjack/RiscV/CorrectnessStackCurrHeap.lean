import Flapjack.RiscV.CorrectnessStackOpCurrHeap

/-!
# StackRemove current-heap get/set at the RISC-V boundary

The current-heap fast paths are ordinary or instructions: a get copies the
configured current-heap register, while a set writes the source value back to
that register.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveGetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (destination : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers config.currHeap))
      (executeInstructions target
        [.or ⟨destination, hdestination⟩
          ⟨config.currHeap, hcurrHeap⟩ ⟨config.currHeap, hcurrHeap⟩]) := by
  simpa [executeInstructions, wordStackMachineBinOp] using
    wordStackRegisterRelation_executeOr source target destination
    config.currHeap config.currHeap hrel hdestination hcurrHeap hcurrHeap
    hdestinationNonzero

theorem executeStackRemoveSetCurrHeap [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hsource : sourceRegister < 32)
    (hcurrHeapNonzero : config.currHeap ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source config.currHeap
        (source.registers sourceRegister))
      (executeInstructions target
        [.or ⟨config.currHeap, hcurrHeap⟩
          ⟨sourceRegister, hsource⟩ ⟨sourceRegister, hsource⟩]) := by
  simpa [executeInstructions, wordStackMachineBinOp] using
    wordStackRegisterRelation_executeOr source target config.currHeap
    sourceRegister sourceRegister hrel hcurrHeap hsource hsource
    hcurrHeapNonzero

theorem compileStackProgramNatToRiscV_getCurrHeap [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.get destination .currHeap : StackProg Nat) =
      some [.or ⟨destination, hdestination⟩
        ⟨config.currHeap, hcurrHeap⟩ ⟨config.currHeap, hcurrHeap⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, labBinOpInstruction, registerOfNat,
    hcurrHeap, hdestination, stackRemoveGet, stackRemoveComplete,
    stackProgDepth, stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_getCurrHeap_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.get destination .currHeap : StackProg Nat) =
      some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers config.currHeap))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_getCurrHeap context config sectionId initialLabel
    destination hcurrHeap hdestination] at hcode
  cases hcode
  exact executeStackRemoveGetCurrHeap config source target destination hcurrHeap
    hdestination hdestinationNonzero hrel

theorem compileStackProgramNatToRiscV_getCurrHeap_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.get destination .currHeap : StackProg Nat) =
      some code) :
    (evalWordStackMachine source
      (stackRemoveGet config destination .currHeap)).map
        (fun final => final.registers destination) =
      some ((executeInstructions target code).registers
        ⟨destination, hdestination⟩) := by
  rw [evalStackRemoveGetCurrHeap config source destination]
  congr 1
  have hsim := compileStackProgramNatToRiscV_getCurrHeap_simulation
    context config sectionId initialLabel destination source target
    hcurrHeap hdestination hdestinationNonzero hrel code hcode
  have hdest := hsim destination hdestination
  simpa [wordStackMachineWriteRegister] using hdest.symm

theorem compileStackProgramNatToRiscV_setCurrHeap [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hsource : sourceRegister < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.set .currHeap sourceRegister : StackProg Nat) =
      some [.or ⟨config.currHeap, hcurrHeap⟩
        ⟨sourceRegister, hsource⟩ ⟨sourceRegister, hsource⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, labBinOpInstruction, registerOfNat,
    hcurrHeap, hsource, stackRemoveSet, stackRemoveComplete,
    stackProgDepth, stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_setCurrHeap_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel sourceRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hcurrHeap : config.currHeap < 32)
    (hsource : sourceRegister < 32)
    (hcurrHeapNonzero : config.currHeap ≠ 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.set .currHeap sourceRegister : StackProg Nat) =
      some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source config.currHeap
        (source.registers sourceRegister))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_setCurrHeap context config sectionId initialLabel
    sourceRegister hcurrHeap hsource] at hcode
  cases hcode
  exact executeStackRemoveSetCurrHeap config source target sourceRegister hcurrHeap
    hsource hcurrHeapNonzero hrel

theorem compileStackProgramNatToRiscV_setCurrHeap_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel sourceRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hcurrHeap : config.currHeap < 32)
    (hsource : sourceRegister < 32)
    (hcurrHeapNonzero : config.currHeap ≠ 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.set .currHeap sourceRegister : StackProg Nat) =
      some code) :
    (evalWordStackMachine source
      (stackRemoveSet config .currHeap sourceRegister)).map
        (fun final => final.registers config.currHeap) =
      some ((executeInstructions target code).registers
        ⟨config.currHeap, hcurrHeap⟩) := by
  rw [evalStackRemoveSetCurrHeap config source sourceRegister]
  congr 1
  have hsim := compileStackProgramNatToRiscV_setCurrHeap_simulation
    context config sectionId initialLabel sourceRegister source target
    hcurrHeap hsource hcurrHeapNonzero hrel code hcode
  have hcurr := hsim config.currHeap hcurrHeap
  simpa [wordStackMachineWriteRegister] using hcurr.symm

end Flapjack.RiscV
