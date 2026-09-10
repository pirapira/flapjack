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

end Flapjack.RiscV
