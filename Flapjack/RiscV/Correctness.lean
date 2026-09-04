import Flapjack.RiscV.Backend
import Flapjack.RiscV.PanSemantics

/-!
Register-level correctness for the RISC-V lowering of Pancake's `AddCarry`
primitive.  This is the first backend theorem that connects the emitted
instruction sequence to the source-level word operation.
-/

namespace Flapjack.RiscV

theorem executeInstructions_addCarry [NeZero width] (state : State width)
    (zero : readRegister state 0 = 0) :
    (readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) 5,
      readRegister
        (executeInstructions state
          [.sltu 31 0 4, .add 5 2 3, .sltu 6 5 3, .add 5 5 31,
            .sltu 31 5 31, .or 6 6 31]) 6) =
      addCarryWords (readRegister state 2) (readRegister state 3)
        (readRegister state 4) := by
  have zero' : state.registers 0 = 0 := by
    simpa [readRegister] using zero
  by_cases firstCarry : state.registers 2 + state.registers 3 < state.registers 3
  · by_cases secondCarry :
        state.registers 2 + state.registers 3 +
            (if 0#width < state.registers 4 then 1#width else 0#width) <
          (if 0#width < state.registers 4 then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
  · by_cases secondCarry :
        state.registers 2 + state.registers 3 +
            (if 0#width < state.registers 4 then 1#width else 0#width) <
          (if 0#width < state.registers 4 then 1#width else 0#width)
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]
    · simp [executeInstructions, execute, writeRegister, nextPc, readRegister,
        zero', firstCarry, secondCarry, addCarryWords_riscv_formula]

end Flapjack.RiscV
