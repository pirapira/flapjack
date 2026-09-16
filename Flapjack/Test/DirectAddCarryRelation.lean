import Flapjack.RiscV.CorrectnessDirectAddCarry
import Flapjack.Test.AddCarrySpillRelation

/-! Regression coverage for public fully spilled AddCarry lowering. -/

namespace Flapjack.RiscV

/-! Under the Cake staging discipline the fully spilled five-register
    `AddCarry` has no staging register left for the carry input, so the
    lowering fails explicitly and the machine state is unchanged; every
    value, including both destinations' old contents, is preserved. -/

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      addCarrySpillValues name = some value →
      wordStackLocation addCarrySpillConfig name = some location →
      wordStackMachineValue addCarrySpillConfig
        (((wordToStackProg (α := Nat) addCarrySpillConfig
          (.inst (.arith (.addCarry 0 1 2 3 4)))).bind
          (evalWordStackMachine addCarrySpillState)).getD addCarrySpillState)
        name = some value := by
  intro name value location _ _ hvalue hlocation
  have hcompiled :
      wordToStackProg (α := Nat) addCarrySpillConfig
        (.inst (.arith (.addCarry 0 1 2 3 4))) = none := by
    simp [addCarrySpillConfig, wordToStackProg, wordToStackInst,
      wordStackArithInst, wordStackAddCarryInst, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLongMulAliasLocationsSafe, wordStackLongMulMoveToPhysical,
      wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
      wordStackOffset, wordSpecialArithLocationsSafe, lookupNatInfo]
  simp only [hcompiled, Option.bind_none, Option.getD]
  by_cases hname : name = 5
  · subst name
    simp [addCarrySpillValues] at hvalue
    subst value
    simp [addCarrySpillConfig, addCarrySpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · exact absurd hvalue (by simp [addCarrySpillValues])

end Flapjack.RiscV
