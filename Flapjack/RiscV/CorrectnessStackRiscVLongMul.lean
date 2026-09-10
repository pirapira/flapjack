import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# StackLang long multiplication at the RISC-V boundary

Long multiplication writes its high result before its low result.  The
high-result destination therefore must not alias either source; the low
destination may be a source because both operands have already been read by
the second instruction.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordStackRegisterRelation_executeLongMul
    [NeZero width] (source : WordStackMachineState width)
    (target : State width)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestinationLeft : destinationLeft < 32)
    (hdestinationRight : destinationRight < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hdestinationLeftNonzero : destinationLeft ≠ 0)
    (hdestinationRightNonzero : destinationRight ≠ 0)
    (hdestinationDistinct : destinationLeft ≠ destinationRight)
    (hdestinationLeftSourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeftSourceRight : destinationLeft ≠ sourceRight) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister source destinationLeft
          (BitVec.ofNat width
            ((source.registers sourceLeft).toNat *
              (source.registers sourceRight).toNat / 2 ^ width))
        )
        destinationRight
          (source.registers sourceLeft * source.registers sourceRight))
      (executeInstructions target
        [.mulHU ⟨destinationLeft, hdestinationLeft⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
         .mul ⟨destinationRight, hdestinationRight⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩]) := by
  have hsourceLeftValue := hrel sourceLeft hsourceLeft
  have hsourceRightValue := hrel sourceRight hsourceRight
  intro register hregister
  have htargetValue := hrel register hregister
  by_cases hleft : register = destinationLeft
  · subst register
    have hleftRightFin :
        (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
          ⟨destinationRight, hdestinationRight⟩ := by
      intro heq
      apply hdestinationDistinct
      exact congrArg Fin.val heq
    have hleftNonzero :
        (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠ 0 := by
      intro heq
      apply hdestinationLeftNonzero
      exact congrArg Fin.val heq
    have hrightNonzero :
        (⟨destinationRight, hdestinationRight⟩ : Fin 32) ≠ 0 := by
      intro heq
      apply hdestinationRightNonzero
      exact congrArg Fin.val heq
    simp [wordStackMachineWriteRegister, executeInstructions, execute,
      writeRegister, readRegister, hsourceLeftValue, hsourceRightValue,
      hleftNonzero, hrightNonzero, hdestinationDistinct]
  · by_cases hright : register = destinationRight
    · subst register
      have hleftSourceLeftFin :
          (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
            ⟨sourceLeft, hsourceLeft⟩ := by
        intro heq
        apply hdestinationLeftSourceLeft
        exact congrArg Fin.val heq
      have hleftSourceRightFin :
          (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
            ⟨sourceRight, hsourceRight⟩ := by
        intro heq
        apply hdestinationLeftSourceRight
        exact congrArg Fin.val heq
      have hleftNonzero :
          (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠ 0 := by
        intro heq
        apply hdestinationLeftNonzero
        exact congrArg Fin.val heq
      have hrightNonzero :
          (⟨destinationRight, hdestinationRight⟩ : Fin 32) ≠ 0 := by
        intro heq
        apply hdestinationRightNonzero
        exact congrArg Fin.val heq
      simp [wordStackMachineWriteRegister, executeInstructions, execute,
        writeRegister, readRegister, hsourceLeftValue, hsourceRightValue,
        hleftNonzero, hrightNonzero,
        Ne.symm hdestinationLeftSourceLeft,
        Ne.symm hdestinationLeftSourceRight]
    · have hregisterLeft :
          (⟨register, hregister⟩ : Fin 32) ≠
            ⟨destinationLeft, hdestinationLeft⟩ := by
        intro heq
        apply hleft
        exact congrArg Fin.val heq
      have hregisterRight :
          (⟨register, hregister⟩ : Fin 32) ≠
            ⟨destinationRight, hdestinationRight⟩ := by
        intro heq
        apply hright
        exact congrArg Fin.val heq
      have hleftNonzero :
          (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠ 0 := by
        intro heq
        apply hdestinationLeftNonzero
        exact congrArg Fin.val heq
      have hrightNonzero :
          (⟨destinationRight, hdestinationRight⟩ : Fin 32) ≠ 0 := by
        intro heq
        apply hdestinationRightNonzero
        exact congrArg Fin.val heq
      simp [wordStackMachineWriteRegister, executeInstructions, execute,
        writeRegister, readRegister, hsourceLeftValue, hsourceRightValue,
        hleftNonzero, hrightNonzero, htargetValue, hleft, hright,
        hregisterLeft, hregisterRight]

theorem evalWordStackMachine_longMul [NeZero width]
    (state : WordStackMachineState width)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat) :
    evalWordStackMachine state
      (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) :
        StackProg Nat) =
      some (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister state destinationLeft
          (BitVec.ofNat width
            ((state.registers sourceLeft).toNat *
              (state.registers sourceRight).toNat / 2 ^ width)))
        destinationRight (state.registers sourceLeft * state.registers sourceRight)) := by
  rfl

theorem compileStackProgramNatToRiscV_longMul [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (hdestinationLeft : destinationLeft < 32)
    (hdestinationRight : destinationRight < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hdestinationLeftSourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeftSourceRight : destinationLeft ≠ sourceRight) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) :
        StackProg Nat) =
      some [.mulHU ⟨destinationLeft, hdestinationLeft⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
        .mul ⟨destinationRight, hdestinationRight⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, wordArithToInstructions,
    registerOfNat, hdestinationLeft, hdestinationRight, hsourceLeft,
    hsourceRight, hdestinationLeftSourceLeft, hdestinationLeftSourceRight,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel]

theorem compileStackProgramNatToRiscV_longMul_register_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hrel : WordStackRegisterRelation source target)
    (hdestinationLeft : destinationLeft < 32)
    (hdestinationRight : destinationRight < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hdestinationLeftNonzero : destinationLeft ≠ 0)
    (hdestinationRightNonzero : destinationRight ≠ 0)
    (hdestinationDistinct : destinationLeft ≠ destinationRight)
    (hdestinationLeftSourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeftSourceRight : destinationLeft ≠ sourceRight)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel
      (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight)) :
        StackProg Nat) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister source destinationLeft
          (BitVec.ofNat width
            ((source.registers sourceLeft).toNat *
              (source.registers sourceRight).toNat / 2 ^ width)))
        destinationRight (source.registers sourceLeft * source.registers sourceRight))
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_longMul context config sectionId initialLabel
    destinationLeft destinationRight sourceLeft sourceRight hdestinationLeft
    hdestinationRight hsourceLeft hsourceRight hdestinationLeftSourceLeft
    hdestinationLeftSourceRight] at hcode
  cases hcode
  exact wordStackRegisterRelation_executeLongMul source target destinationLeft
    destinationRight sourceLeft sourceRight hrel hdestinationLeft hdestinationRight
    hsourceLeft hsourceRight hdestinationLeftNonzero hdestinationRightNonzero
    hdestinationDistinct hdestinationLeftSourceLeft hdestinationLeftSourceRight

end Flapjack.RiscV
