import Flapjack.RiscV.WordToStack

/-!
# StackLang `LongDiv` correctness

CakeML normalizes double-width division to the fixed `x3:x0` dividend
convention.  The Word-to-Stack pass may load the divisor from a spill slot,
but the abstract StackLang machine must still produce the same quotient and
remainder.  This is the executable correctness boundary used before the
layout-aware RISC-V runtime convention is connected.
-/

namespace Flapjack.RiscV

theorem evalWordStackMachine_longDiv_preserves_values [NeZero width]
    (config : WordStackConfig) (state final : WordStackMachineState width)
    (divisor : Nat)
    (divisorLocation' : WordLocation)
    (leftValue rightValue divisorValue : Word width)
    (hzero : wordStackLocation config 0 = some (.register 0))
    (hthree : wordStackLocation config 3 = some (.register 3))
    (hdivisor : wordStackLocation config divisor = some divisorLocation')
    (hleftValue : wordStackMachineValue config state 3 = some leftValue)
    (hrightValue : wordStackMachineValue config state 0 = some rightValue)
    (hdivisorValue : wordStackMachineValue config state divisor =
      some divisorValue)
    (hscratchZero : config.scratch ≠ 0)
    (hscratchThree : config.scratch ≠ 3)
    (heval : (wordStackLongDivInst config (.longDiv 0 3 3 0 divisor)).bind
      (evalWordStackMachine state) = some final) :
    wordStackMachineValue config final 0 =
        (wordStackLongDivResult leftValue rightValue divisorValue).map
          (fun result => result.1) ∧
      wordStackMachineValue config final 3 =
        (wordStackLongDivResult leftValue rightValue divisorValue).map
          (fun result => result.2) := by
  change lookupNatInfo 0 config.locations = some (.register 0) at hzero
  change lookupNatInfo 3 config.locations = some (.register 3) at hthree
  change lookupNatInfo divisor config.locations = some divisorLocation' at hdivisor
  cases divisorLocation' with
  | register divisorRegister =>
      by_cases hdivisorZero : divisorRegister = 0
      · simp [wordStackLongDivInst, wordStackLocation, hdivisor,
          hdivisorZero] at heval
      · by_cases hdivisorThree : divisorRegister = 3
        · simp [wordStackLongDivInst, wordStackLocation, hdivisor,
            hdivisorThree] at heval
        · have hleftReg : state.registers 3 = leftValue := by
            simpa [wordStackMachineValue, wordStackLocation, hthree] using
              hleftValue
          have hrightReg : state.registers 0 = rightValue := by
            simpa [wordStackMachineValue, wordStackLocation, hzero] using
              hrightValue
          have hdivisorReg : state.registers divisorRegister = divisorValue := by
            simpa [wordStackMachineValue, wordStackLocation, hdivisor] using
              hdivisorValue
          cases hresult : wordStackLongDivResult leftValue rightValue divisorValue with
          | none =>
              simp [wordStackLongDivInst, wordStackLocation, hdivisor,
                hdivisorZero, hdivisorThree, evalWordStackMachine,
                hleftReg, hrightReg, hdivisorReg, hresult] at heval
          | some result =>
              rcases result with ⟨quotient, remainder⟩
              simp [wordStackLongDivInst, wordStackLocation, hdivisor,
                hdivisorZero, hdivisorThree, evalWordStackMachine,
                hleftReg, hrightReg, hdivisorReg, hresult] at heval
              cases heval
              constructor <;>
                simp [wordStackMachineValue, wordStackLocation,
                  wordStackMachineWriteRegister, hzero, hthree]
  | stack divisorSlot =>
      have hleftReg : state.registers 3 = leftValue := by
        simpa [wordStackMachineValue, wordStackLocation, hthree] using
          hleftValue
      have hrightReg : state.registers 0 = rightValue := by
        simpa [wordStackMachineValue, wordStackLocation, hzero] using
          hrightValue
      have hthreeScratch : ¬(3 = config.scratch) := Ne.symm hscratchThree
      have hzeroScratch : ¬(0 = config.scratch) := Ne.symm hscratchZero
      have hdivisorStack : state.stack (config.stackBase + divisorSlot) =
          divisorValue := by
        simpa [wordStackMachineValue, wordStackLocation, wordStackOffset,
          hdivisor] using hdivisorValue
      cases hresult : wordStackLongDivResult leftValue rightValue divisorValue with
      | none =>
          simp [wordStackLongDivInst, wordStackLocation, wordStackOffset,
            hdivisor, evalWordStackMachine, wordStackMachineWriteRegister,
            hleftReg, hrightReg, hdivisorStack, hthreeScratch, hzeroScratch] at heval
          rw [hresult] at heval
          simp at heval
      | some result =>
          rcases result with ⟨quotient, remainder⟩
          simp [wordStackLongDivInst, wordStackLocation, wordStackOffset,
            hdivisor, evalWordStackMachine, wordStackMachineWriteRegister,
            hleftReg, hrightReg, hdivisorStack, hthreeScratch, hzeroScratch] at heval
          rw [hresult] at heval
          cases heval
          constructor <;>
            simp [wordStackMachineValue, wordStackLocation, hzero, hthree]

end Flapjack.RiscV
