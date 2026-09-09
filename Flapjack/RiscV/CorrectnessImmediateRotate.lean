import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# Immediate rotate-right lowering at the RISC-V boundary

The backend implements an immediate rotate-right with a right shift, a
complementary left shift, and an OR.  The temporary is x31, so the contract
uses the register relation that excludes that scratch register.
-/

namespace Flapjack.RiscV

theorem wordStackRegisterRelation_executeRorImmediate
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left : Nat) (amount : Word width)
    (hrel : WordStackRegisterRelationExceptX31 source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hleftScratch : left ≠ 31) :
    WordStackRegisterRelationExceptX31
      (wordStackMachineWriteRegister source destination
        (wordStackMachineShift .ror (source.registers left) amount))
      (executeInstructions target
        [.srli 31 ⟨left, hleft⟩ (shiftAmount amount),
         .slli ⟨destination, hdestination⟩ ⟨left, hleft⟩
           (BitVec.ofNat width ((width - shiftAmount amount) % width)),
         .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]) := by
  have hleftValue := hrel left hleft hleftScratch
  have hdestinationFinNonzero :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  have hdestinationFinScratch :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hdestinationScratch
    exact congrArg Fin.val heq
  have hleftFinScratch :
      (⟨left, hleft⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hleftScratch
    exact congrArg Fin.val heq
  have amount_lt : shiftAmount amount < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  have complement_lt : (width - shiftAmount amount) % width < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  have htargetDestination :
      (executeInstructions target
        [.srli 31 ⟨left, hleft⟩ (shiftAmount amount),
         .slli ⟨destination, hdestination⟩ ⟨left, hleft⟩
           (BitVec.ofNat width ((width - shiftAmount amount) % width)),
         .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
          ⟨destination, hdestination⟩ =
      wordStackMachineShift .ror (source.registers left) amount := by
    simp [executeInstructions, execute, readRegister, writeRegister,
      wordStackMachineShift, wordStackMachineRotateRight, hleftValue,
      hleftFinScratch, hdestinationFinNonzero,
      Ne.symm hdestinationFinScratch]
    rw [shiftAmount_ofNat_of_lt complement_lt,
      shiftAmount_ofNat_of_lt amount_lt]
    simp [shiftAmount, BitVec.or_comm]
  intro register hregister hregisterScratch
  have htarget := hrel register hregister hregisterScratch
  by_cases hsame : register = destination
  · subst register
    simpa [wordStackMachineWriteRegister] using htargetDestination
  · have hfin : (⟨register, hregister⟩ : Fin 32) ≠
        ⟨destination, hdestination⟩ := by
      intro heq
      apply hsame
      exact congrArg Fin.val heq
    have hregisterFinScratch :
        (⟨register, hregister⟩ : Fin 32) ≠ 31 := by
      intro heq
      apply hregisterScratch
      exact congrArg Fin.val heq
    have htargetPreserved :
        (executeInstructions target
          [.srli 31 ⟨left, hleft⟩ (shiftAmount amount),
           .slli ⟨destination, hdestination⟩ ⟨left, hleft⟩
             (BitVec.ofNat width ((width - shiftAmount amount) % width)),
           .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
            ⟨register, hregister⟩ = target.registers ⟨register, hregister⟩ := by
      simp [executeInstructions, execute, writeRegister, hfin,
        hregisterFinScratch, hdestinationFinNonzero]
    calc
      (executeInstructions target
          [.srli 31 ⟨left, hleft⟩ (shiftAmount amount),
           .slli ⟨destination, hdestination⟩ ⟨left, hleft⟩
             (BitVec.ofNat width ((width - shiftAmount amount) % width)),
           .or ⟨destination, hdestination⟩ ⟨destination, hdestination⟩ 31]).registers
            ⟨register, hregister⟩ = target.registers ⟨register, hregister⟩ :=
        htargetPreserved
      _ = source.registers register := htarget
      _ = (wordStackMachineWriteRegister source destination
          (wordStackMachineShift .ror (source.registers left) amount)).registers
            register := by
        simp [wordStackMachineWriteRegister, hsame]

theorem compileWordImmediateRotateRight_sound [NeZero width]
    (state : State width) (amount : Word width) :
    evalWordProg state
        (.assign 1 (.shift .ror (.var 2) (.const amount))) =
      some (executeInstructions state
        [.srli 31 2 (shiftAmount amount),
         .slli 1 2 (BitVec.ofNat width ((width - shiftAmount amount) % width)),
         .or 1 1 31]) := by
  simp [evalWordProg, wordExpToInstructions,
    registerOfNat, executeInstructions]

end Flapjack.RiscV
