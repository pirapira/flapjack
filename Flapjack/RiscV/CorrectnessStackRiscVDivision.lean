import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# StackLang division at the RISC-V boundary

CakeML's unsigned division has a defined result for a zero divisor.  The
StackLang evaluator and the RISC-V model use the same result, so expose that
agreement together with the corresponding Lab lowering.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordStackRegisterRelation_executeDivU
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination dividend divisor : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdividend : dividend < 32)
    (hdivisor : divisor < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (if source.registers divisor == 0 then
          BitVec.ofNat width (2 ^ width - 1)
        else
          BitVec.ofNat width
            (source.registers dividend).toNat / (source.registers divisor).toNat))
      (execute target (.divU ⟨destination, hdestination⟩
        ⟨dividend, hdividend⟩ ⟨divisor, hdivisor⟩)) := by
  have hdividendValue := hrel dividend hdividend
  have hdivisorValue := hrel divisor hdivisor
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (if source.registers divisor == 0 then
        BitVec.ofNat width (2 ^ width - 1)
      else
        BitVec.ofNat width
          (source.registers dividend).toNat / (source.registers divisor).toNat))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (if target.registers ⟨divisor, hdivisor⟩ == 0 then
        BitVec.ofNat width (2 ^ width - 1)
      else
        BitVec.ofNat width
          (target.registers ⟨dividend, hdividend⟩).toNat /
            (target.registers ⟨divisor, hdivisor⟩).toNat))
  rw [hdividendValue, hdivisorValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (if source.registers divisor == 0 then
      BitVec.ofNat width (2 ^ width - 1)
    else
      BitVec.ofNat width
        (source.registers dividend).toNat / (source.registers divisor).toNat)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem labCompilePlain_div
    [NeZero width] (destination dividend divisor : Nat)
    (hdestination : destination < 32) (hdividend : dividend < 32)
    (hdivisor : divisor < 32) :
    labCompilePlain
      (.word (.arith (.div destination dividend divisor)) :
        LabPlain (Word width)) =
      some [.divU ⟨destination, hdestination⟩
        ⟨dividend, hdividend⟩ ⟨divisor, hdivisor⟩] := by
  simp [labCompilePlain, wordArithToInstructions, wordArithToInstruction,
    registerOfNat, hdestination, hdividend, hdivisor]

theorem labCompilePlain_div_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination dividend divisor : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdividend : dividend < 32)
    (hdivisor : divisor < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.word (.arith (.div destination dividend divisor)) :
        LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (if source.registers divisor == 0 then
          BitVec.ofNat width (2 ^ width - 1)
        else
          BitVec.ofNat width
            (source.registers dividend).toNat / (source.registers divisor).toNat))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_div (width := width) destination dividend divisor
    hdestination hdividend hdivisor
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (if source.registers divisor == 0 then
        BitVec.ofNat width (2 ^ width - 1)
      else
        BitVec.ofNat width
          (source.registers dividend).toNat / (source.registers divisor).toNat))
    (execute target (.divU ⟨destination, hdestination⟩
      ⟨dividend, hdividend⟩ ⟨divisor, hdivisor⟩))
  exact wordStackRegisterRelation_executeDivU source target destination dividend divisor
    hrel hdestination hdividend hdivisor hdestinationNonzero

end Flapjack.RiscV
