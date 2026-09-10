import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# StackRemove current-heap operations at the RISC-V boundary

StackRemove lowers OpCurrHeap to an ordinary register binary operation.
This contract packages the five binary-operation cases behind the
StackRemove-specific source-state update.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveOpCurrHeap [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (operator : BinOp)
    (destination sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineBinOp operator
          (source.registers sourceRegister)
          (source.registers config.currHeap)))
      (executeInstructions target
        (match operator with
        | .add =>
            [.add ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .sub =>
            [.sub ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .and =>
            [.and ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .or =>
            [.or ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .xor =>
            [.xor ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩])) := by
  cases operator with
  | add =>
      exact wordStackRegisterRelation_executeAdd source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | sub =>
      exact wordStackRegisterRelation_executeSub source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | and =>
      exact wordStackRegisterRelation_executeAnd source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | or =>
      exact wordStackRegisterRelation_executeOr source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | xor =>
      exact wordStackRegisterRelation_executeXor source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero

theorem compileStackProgramNatToRiscV_opCurrHeap [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (operator : BinOp) (sectionId initialLabel destination sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hsource : sourceRegister < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.opCurrHeap operator destination sourceRegister : StackProg Nat) =
      some [match operator with
        | .add => .add ⟨destination, hdestination⟩ ⟨sourceRegister, hsource⟩
            ⟨config.currHeap, hcurrHeap⟩
        | .sub => .sub ⟨destination, hdestination⟩ ⟨sourceRegister, hsource⟩
            ⟨config.currHeap, hcurrHeap⟩
        | .and => .and ⟨destination, hdestination⟩ ⟨sourceRegister, hsource⟩
            ⟨config.currHeap, hcurrHeap⟩
        | .or => .or ⟨destination, hdestination⟩ ⟨sourceRegister, hsource⟩
            ⟨config.currHeap, hcurrHeap⟩
        | .xor => .xor ⟨destination, hdestination⟩ ⟨sourceRegister, hsource⟩
            ⟨config.currHeap, hcurrHeap⟩] := by
  cases operator <;>
    simp [compileStackProgramNatToRiscV, compileLabSectionNat,
      compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
      labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
      labLabel, labCompileLines, labCompilePlain, labCollectLabels,
      labLineInstructionCount, labBinOpInstruction, registerOfNat,
      hcurrHeap, hdestination, hsource, stackRemoveOpCurrHeap,
      stackRemoveComplete, stackProgDepth, stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_opCurrHeap_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (operator : BinOp) (sectionId initialLabel destination sourceRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel
        (.opCurrHeap operator destination sourceRegister : StackProg Nat) =
      some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineBinOp operator
          (source.registers sourceRegister)
          (source.registers config.currHeap)))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_opCurrHeap context config operator sectionId
    initialLabel destination sourceRegister hcurrHeap hdestination hsource] at hcode
  cases hcode
  cases operator <;>
    exact executeStackRemoveOpCurrHeap config source target _ destination
      sourceRegister hcurrHeap hdestination hsource hdestinationNonzero hrel

end Flapjack.RiscV
