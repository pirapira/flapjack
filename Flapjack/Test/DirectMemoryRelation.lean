import Flapjack.RiscV.CorrectnessDirectMemory
import Flapjack.Test.MemorySpillRelation

/-! Regression coverage for public memory load/store spill lowering. -/

namespace Flapjack.RiscV

/- Cake's `wReg1` uses the first allocator register as the carrier when the
   address of a store is spilled.  This small case is the source-level shape
   that exposed the four-byte RISC-V parity discrepancy in the differential
   reducer: using the link register is semantically valid but not
   Pancake-compatible. -/

example :
    wordStackMemoryInst
        { locations := [(0, .stack 19), (21, .register 21)],
          scratch := 22, stackBase := 0, addressScratch := 23 }
        .store 21 0 =
      some (.seq (.stackLoad 22 19)
        (.inst (.mem .store 21 22)) : StackProg Nat) := by
  simp [wordStackMemoryInst, wordStackStoreInst, wordStackStoreAddressRegister,
    wordStackLocation, wordStackOffset, lookupNatInfo]

example :
    wordStackMappedValuesExcept memorySpillConfig 1 memorySpillValues
      (((wordToStackProg (α := Nat) memorySpillConfig
        (.inst (.mem .load 1 2))).bind
        (evalWordStackMachine memorySpillState)).getD memorySpillState) := by
  apply evalWordStackMachine_direct_load_preserves_unrelated_values
    (config := memorySpillConfig) (state := memorySpillState)
    (final := ((wordToStackProg (α := Nat) memorySpillConfig
      (.inst (.mem .load 1 2))).bind
      (evalWordStackMachine memorySpillState)).getD memorySpillState)
    (destination := 1) (address := 2)
    (destinationLocation := .stack 0) (addressLocation := .stack 1)
    (values := memorySpillValues)
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        simp [memorySpillConfig, memorySpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · simp [memorySpillConfig, memorySpillState, wordToStackProg,
      wordToStackInst, wordStackMemoryInst, wordStackLoadInst,
      wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

example :
    wordStackMappedValues memorySpillConfig memorySpillValues
      (((wordToStackProg (α := Nat) memorySpillConfig
        (.store (.var 3) 2)).bind
        (evalWordStackMachine memorySpillState)).getD memorySpillState) := by
  apply evalWordStackMachine_direct_store_preserves_mapped_values
    (config := memorySpillConfig) (state := memorySpillState)
    (final := ((wordToStackProg (α := Nat) memorySpillConfig
      (.store (.var 3) 2)).bind
      (evalWordStackMachine memorySpillState)).getD memorySpillState)
    (source := 2) (address := 3)
    (sourceLocation := .stack 1) (addressLocation := .register 6)
    (values := memorySpillValues)
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        simp [memorySpillConfig, wordStackStoreAddressRegister]
      · simp [memorySpillValues] at hvalue
  · simp [memorySpillConfig, memorySpillState, wordToStackProg,
      wordStackMemoryInst, wordStackStoreInst, wordStackLocation,
      wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, lookupNatInfo, Option.bind, Option.getD]
