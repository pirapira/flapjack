import Flapjack.RiscV.CorrectnessAddCarrySpill

/-! Regression coverage for the fully spilled AddCarry lowering. -/

namespace Flapjack.RiscV

def addCarrySpillConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3), (2, .stack 4),
      (3, .stack 5), (4, .stack 6), (5, .register 6)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def addCarrySpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 14 then BitVec.ofNat 8 255
      else if offset = 15 then BitVec.ofNat 8 1
      else if offset = 16 then BitVec.ofNat 8 1 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def addCarrySpillValues : Nat → Option (Word 8)
  | 5 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues addCarrySpillConfig addCarrySpillValues
      addCarrySpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 5
  · subst name
    simp [addCarrySpillValues] at hvalue
    subst value
    simp [addCarrySpillConfig, addCarrySpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [addCarrySpillValues] at hvalue

/-! With the Cake staging discipline (`wReg1`/`wReg2`/`wRegWrite1`,
    `word_to_stackScript.sml:28-56`) the three spilled sources of a fully
    spilled five-register `AddCarry` have no staging register left, so the
    lowering fails explicitly — Cake never stages the carry input `n4` and
    therefore never faces this configuration. -/

example :
    (wordStackAddCarryInst (α := Nat) addCarrySpillConfig
      (.addCarry 0 1 2 3 4)) = none := by
  simp [addCarrySpillConfig, wordStackAddCarryInst, wordStackLocation,
    lookupNatInfo]

def addCarryMixedConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3), (2, .stack 4),
      (3, .stack 5), (4, .register 5), (5, .register 6)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def addCarryMixedState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 5 then BitVec.ofNat 8 1
      else if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 14 then BitVec.ofNat 8 255
      else if offset = 15 then BitVec.ofNat 8 1 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    let final := ((wordStackAddCarryInst addCarryMixedConfig
      (.addCarry 0 1 2 3 4)).bind
      (evalWordStackMachine addCarryMixedState)).getD addCarryMixedState
    wordStackMachineValue addCarryMixedConfig final 0 =
        some (BitVec.ofNat 8 1) ∧
      wordStackMachineValue addCarryMixedConfig final 1 =
        some (BitVec.ofNat 8 1) ∧
      -- a register-resident bystander keeps its value
      wordStackMachineValue addCarryMixedConfig final 5 =
        some (BitVec.ofNat 8 23) := by
  simp [addCarryMixedConfig, addCarryMixedState, wordStackAddCarryInst,
    wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
    wordStackJoin, wordStackLocation, wordStackOffset,
    evalWordStackMachine, wordStackMachineWriteRegister,
    wordStackMachineWriteSlot, wordStackMachineValue, lookupNatInfo]

end Flapjack.RiscV
