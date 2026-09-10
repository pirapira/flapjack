import Flapjack.RiscV.CorrectnessStackRiscV
import Flapjack.RiscV.Correctness

/-!
# StackLang AddCarry at the RISC-V boundary

The six-instruction AddCarry lowering uses x31 as a temporary.  Consequently
the relation is stated modulo x31, while the two result registers and all
operands remain related exactly.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordStackRegisterRelationExceptX31_executeAddCarry
    [NeZero width] (source : WordStackMachineState width)
    (target : State width)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (hrel : WordStackRegisterRelationExceptX31 source target)
    (hdestination : destination < 32) (hresultCarry : resultCarry < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hcarryIn : carryIn < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hresultCarryNonzero : resultCarry ≠ 0)
    (hdestinationDistinct : destination ≠ resultCarry)
    (hdestinationSourceRight : destination ≠ sourceRight)
    (hdestinationScratch : destination ≠ 31)
    (hresultCarryScratch : resultCarry ≠ 31)
    (hsourceLeftScratch : sourceLeft ≠ 31)
    (hsourceRightScratch : sourceRight ≠ 31)
    (hcarryInScratch : carryIn ≠ 31)
    (hzero : source.registers 0 = 0) :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister source destination
          (addCarryWords (source.registers sourceLeft)
            (source.registers sourceRight)
            (source.registers carryIn)).1)
        resultCarry
          (addCarryWords (source.registers sourceLeft)
            (source.registers sourceRight)
            (source.registers carryIn)).2)
      (executeInstructions target
        [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
         .add ⟨destination, hdestination⟩
           ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
         .sltu ⟨resultCarry, hresultCarry⟩
           ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
         .add ⟨destination, hdestination⟩
           ⟨destination, hdestination⟩ 31,
         .sltu 31 ⟨destination, hdestination⟩ 31,
         .or ⟨resultCarry, hresultCarry⟩
           ⟨resultCarry, hresultCarry⟩ 31]) := by
  have hzeroTarget : target.registers 0 = 0 := by
    have hz := hrel 0 (by omega) (by omega)
    calc
      target.registers 0 = source.registers 0 := hz
      _ = 0 := hzero
  have hsourceLeftValue := hrel sourceLeft hsourceLeft hsourceLeftScratch
  have hsourceRightValue := hrel sourceRight hsourceRight hsourceRightScratch
  have hcarryInValue := hrel carryIn hcarryIn hcarryInScratch
  have hresult := executeInstructions_addCarry_general target
    ⟨destination, hdestination⟩ ⟨resultCarry, hresultCarry⟩
    ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩
    ⟨carryIn, hcarryIn⟩ (by simpa [readRegister] using hzeroTarget)
    (by intro heq; apply hdestinationNonzero; exact congrArg Fin.val heq)
    (by intro heq; apply hresultCarryNonzero; exact congrArg Fin.val heq)
    (by intro heq; apply hdestinationDistinct; exact congrArg Fin.val heq)
    (by intro heq; apply hdestinationSourceRight; exact congrArg Fin.val heq)
    (by intro heq; apply hdestinationScratch; exact congrArg Fin.val heq)
    (by intro heq; apply hresultCarryScratch; exact congrArg Fin.val heq)
    (by intro heq; apply hsourceLeftScratch; exact congrArg Fin.val heq)
    (by intro heq; apply hsourceRightScratch; exact congrArg Fin.val heq)
    (by intro heq; apply hcarryInScratch; exact congrArg Fin.val heq)
  have hresultLeft :
      readRegister
          (executeInstructions target
            [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
             .add ⟨destination, hdestination⟩
               ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
             .sltu ⟨resultCarry, hresultCarry⟩
               ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
             .add ⟨destination, hdestination⟩
               ⟨destination, hdestination⟩ 31,
             .sltu 31 ⟨destination, hdestination⟩ 31,
             .or ⟨resultCarry, hresultCarry⟩
               ⟨resultCarry, hresultCarry⟩ 31])
          ⟨destination, hdestination⟩ =
        (addCarryWords (source.registers sourceLeft)
          (source.registers sourceRight) (source.registers carryIn)).1 := by
    calc
      _ = (addCarryWords (target.registers ⟨sourceLeft, hsourceLeft⟩)
          (target.registers ⟨sourceRight, hsourceRight⟩)
          (target.registers ⟨carryIn, hcarryIn⟩)).1 :=
        congrArg Prod.fst hresult
      _ = _ := by rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
  have hresultCarryValue :
      readRegister
          (executeInstructions target
            [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
             .add ⟨destination, hdestination⟩
               ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
             .sltu ⟨resultCarry, hresultCarry⟩
               ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
             .add ⟨destination, hdestination⟩
               ⟨destination, hdestination⟩ 31,
             .sltu 31 ⟨destination, hdestination⟩ 31,
             .or ⟨resultCarry, hresultCarry⟩
               ⟨resultCarry, hresultCarry⟩ 31])
          ⟨resultCarry, hresultCarry⟩ =
        (addCarryWords (source.registers sourceLeft)
          (source.registers sourceRight) (source.registers carryIn)).2 := by
    calc
      _ = (addCarryWords (target.registers ⟨sourceLeft, hsourceLeft⟩)
          (target.registers ⟨sourceRight, hsourceRight⟩)
          (target.registers ⟨carryIn, hcarryIn⟩)).2 :=
        congrArg Prod.snd hresult
      _ = _ := by rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
  intro register hregister hregisterScratch
  have htargetValue := hrel register hregister hregisterScratch
  by_cases hdestinationRegister : register = destination
  · subst register
    calc
      (executeInstructions target
          [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
           .add ⟨destination, hdestination⟩
             ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
           .sltu ⟨resultCarry, hresultCarry⟩
             ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
           .add ⟨destination, hdestination⟩
             ⟨destination, hdestination⟩ 31,
           .sltu 31 ⟨destination, hdestination⟩ 31,
           .or ⟨resultCarry, hresultCarry⟩
             ⟨resultCarry, hresultCarry⟩ 31]).registers
          ⟨destination, hregister⟩ =
        (addCarryWords (source.registers sourceLeft)
          (source.registers sourceRight) (source.registers carryIn)).1 := by
            simpa [readRegister] using hresultLeft
      _ = (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister source destination
            (addCarryWords (source.registers sourceLeft)
              (source.registers sourceRight) (source.registers carryIn)).1)
          resultCarry
            (addCarryWords (source.registers sourceLeft)
              (source.registers sourceRight) (source.registers carryIn)).2).registers
            destination := by
              simp [wordStackMachineWriteRegister, hdestinationDistinct]
  · by_cases hresultRegister : register = resultCarry
    · subst register
      calc
        (executeInstructions target
            [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
             .add ⟨destination, hdestination⟩
               ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
             .sltu ⟨resultCarry, hresultCarry⟩
               ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
             .add ⟨destination, hdestination⟩
               ⟨destination, hdestination⟩ 31,
             .sltu 31 ⟨destination, hdestination⟩ 31,
             .or ⟨resultCarry, hresultCarry⟩
               ⟨resultCarry, hresultCarry⟩ 31]).registers
            ⟨resultCarry, hregister⟩ =
          (addCarryWords (source.registers sourceLeft)
            (source.registers sourceRight) (source.registers carryIn)).2 := by
              simpa [readRegister] using hresultCarryValue
        _ = (wordStackMachineWriteRegister
            (wordStackMachineWriteRegister source destination
              (addCarryWords (source.registers sourceLeft)
                (source.registers sourceRight) (source.registers carryIn)).1)
            resultCarry
              (addCarryWords (source.registers sourceLeft)
                (source.registers sourceRight) (source.registers carryIn)).2).registers
              resultCarry := by
                simp [wordStackMachineWriteRegister]
    · have hregisterDestination :
          (⟨register, hregister⟩ : Fin 32) ≠
            ⟨destination, hdestination⟩ := by
        intro heq
        apply hdestinationRegister
        exact congrArg Fin.val heq
      have hregisterResult :
          (⟨register, hregister⟩ : Fin 32) ≠
            ⟨resultCarry, hresultCarry⟩ := by
        intro heq
        apply hresultRegister
        exact congrArg Fin.val heq
      have hregisterScratch :
          (⟨register, hregister⟩ : Fin 32) ≠ 31 := by
        intro heq
        apply hregisterScratch
        exact congrArg Fin.val heq
      have hpreserved :
          (executeInstructions target
            [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
             .add ⟨destination, hdestination⟩
               ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
             .sltu ⟨resultCarry, hresultCarry⟩
               ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
             .add ⟨destination, hdestination⟩
               ⟨destination, hdestination⟩ 31,
             .sltu 31 ⟨destination, hdestination⟩ 31,
             .or ⟨resultCarry, hresultCarry⟩
               ⟨resultCarry, hresultCarry⟩ 31]).registers
              ⟨register, hregister⟩ =
            target.registers ⟨register, hregister⟩ := by
        simp [executeInstructions, execute, writeRegister, nextPc,
          hdestinationNonzero, hresultCarryNonzero,
          hregisterDestination, hregisterResult, hregisterScratch]
      calc
        (executeInstructions target
          [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
           .add ⟨destination, hdestination⟩
             ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
           .sltu ⟨resultCarry, hresultCarry⟩
             ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
           .add ⟨destination, hdestination⟩
             ⟨destination, hdestination⟩ 31,
           .sltu 31 ⟨destination, hdestination⟩ 31,
           .or ⟨resultCarry, hresultCarry⟩
             ⟨resultCarry, hresultCarry⟩ 31]).registers
            ⟨register, hregister⟩ =
          target.registers ⟨register, hregister⟩ := by
            simpa [readRegister] using hpreserved
        _ = source.registers register := htargetValue
        _ = (wordStackMachineWriteRegister
          (wordStackMachineWriteRegister source destination
            (addCarryWords (source.registers sourceLeft)
              (source.registers sourceRight) (source.registers carryIn)).1)
          resultCarry
            (addCarryWords (source.registers sourceLeft)
              (source.registers sourceRight) (source.registers carryIn)).2).registers
            register := by
              simp [wordStackMachineWriteRegister,
                hdestinationRegister, hresultRegister]

theorem evalWordStackMachine_addCarry [NeZero width]
    (state : WordStackMachineState width)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat) :
    evalWordStackMachine state
      (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)) :
        StackProg Nat) =
      some (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister state destination
          (addCarryWords (state.registers sourceLeft)
            (state.registers sourceRight) (state.registers carryIn)).1)
        resultCarry
          (addCarryWords (state.registers sourceLeft)
            (state.registers sourceRight) (state.registers carryIn)).2) := by
  let carry : Nat := if state.registers carryIn == 0 then 0 else 1
  let total : Nat := (state.registers sourceLeft).toNat +
    (state.registers sourceRight).toNat + carry
  have hleft : (state.registers sourceLeft).toNat < 2 ^ width :=
    (state.registers sourceLeft).isLt
  have hright : (state.registers sourceRight).toNat < 2 ^ width :=
    (state.registers sourceRight).isLt
  have hcarry : carry ≤ 1 := by
    dsimp [carry]
    split <;> omega
  have htotal : total < 2 ^ width + 2 ^ width := by
    simp [total]
    omega
  have hquotient : total / 2 ^ width = if 2 ^ width ≤ total then 1 else 0 := by
    by_cases h : 2 ^ width ≤ total
    · rw [if_pos h]
      exact Nat.div_eq_of_lt_le (by simpa using h) (by omega)
    · rw [if_neg h]
      exact Nat.div_eq_of_lt (by omega)
  dsimp [total, carry] at hquotient
  have hquotient' :
      ((state.registers sourceLeft).toNat + (state.registers sourceRight).toNat +
          if state.registers carryIn == 0 then 0 else 1) / 2 ^ width =
        if 2 ^ width ≤ (state.registers sourceLeft).toNat +
            (state.registers sourceRight).toNat +
              if state.registers carryIn == 0 then 0 else 1 then 1 else 0 := by
    simpa using hquotient
  simp only [evalWordStackMachine, addCarryWords]
  rw [hquotient']

theorem compileStackProgramNatToRiscV_addCarry [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (hdestination : destination < 32) (hresultCarry : resultCarry < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hcarryIn : carryIn < 32)
    (hdestinationScratch : destination ≠ 31)
    (hresultCarryScratch : resultCarry ≠ 31)
    (hsourceLeftScratch : sourceLeft ≠ 31)
    (hsourceRightScratch : sourceRight ≠ 31)
    (hcarryInScratch : carryIn ≠ 31) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)) :
        StackProg Nat) =
      some [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
        .add ⟨destination, hdestination⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
        .sltu ⟨resultCarry, hresultCarry⟩
          ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
        .add ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31,
        .sltu 31 ⟨destination, hdestination⟩ 31,
        .or ⟨resultCarry, hresultCarry⟩ ⟨resultCarry, hresultCarry⟩ 31] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, wordArithToInstructions,
    registerOfNat, hdestination, hresultCarry, hsourceLeft, hsourceRight,
    hcarryIn, hdestinationScratch, hresultCarryScratch, hsourceLeftScratch,
    hsourceRightScratch, hcarryInScratch,
    stackRemoveComplete, stackProgDepth, stackRemoveFuel]

theorem compileStackProgramNatToRiscV_addCarry_register_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hrel : WordStackRegisterRelationExceptX31 source target)
    (hdestination : destination < 32) (hresultCarry : resultCarry < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hcarryIn : carryIn < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hresultCarryNonzero : resultCarry ≠ 0)
    (hdestinationDistinct : destination ≠ resultCarry)
    (hdestinationSourceRight : destination ≠ sourceRight)
    (hdestinationScratch : destination ≠ 31)
    (hresultCarryScratch : resultCarry ≠ 31)
    (hsourceLeftScratch : sourceLeft ≠ 31)
    (hsourceRightScratch : sourceRight ≠ 31)
    (hcarryInScratch : carryIn ≠ 31)
    (hzero : source.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel
      (.inst (.arith (.addCarry destination resultCarry sourceLeft sourceRight carryIn)) :
        StackProg Nat) = some code) :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister
        (wordStackMachineWriteRegister source destination
          (addCarryWords (source.registers sourceLeft)
            (source.registers sourceRight) (source.registers carryIn)).1)
        resultCarry
          (addCarryWords (source.registers sourceLeft)
            (source.registers sourceRight) (source.registers carryIn)).2)
      (executeInstructions target code) := by
  rw [compileStackProgramNatToRiscV_addCarry context config sectionId initialLabel
    destination resultCarry sourceLeft sourceRight carryIn hdestination hresultCarry
    hsourceLeft hsourceRight hcarryIn hdestinationScratch hresultCarryScratch
    hsourceLeftScratch hsourceRightScratch hcarryInScratch] at hcode
  cases hcode
  exact wordStackRegisterRelationExceptX31_executeAddCarry source target
    destination resultCarry sourceLeft sourceRight carryIn hrel hdestination
    hresultCarry hsourceLeft hsourceRight hcarryIn hdestinationNonzero
    hresultCarryNonzero hdestinationDistinct hdestinationSourceRight
    hdestinationScratch hresultCarryScratch hsourceLeftScratch hsourceRightScratch
    hcarryInScratch hzero

end Flapjack.RiscV
