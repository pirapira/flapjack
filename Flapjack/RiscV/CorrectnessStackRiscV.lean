import Flapjack.RiscV.CorrectnessStack
import Flapjack.RiscV.Lab

/-!
# StackLang register simulation at the RISC-V boundary

`WordStackMachineState` numbers registers with `Nat`, while the RISC-V model
uses the architectural `Fin 32` register file.  This module records the
smallest useful bridge: agreement on all architectural registers.  The first
contract connects StackLang's constant instruction with the exact `addi`
sequence emitted by LabLang and the RISC-V backend.
-/

namespace Flapjack.RiscV

def WordStackRegisterRelation [NeZero width]
    (source : WordStackMachineState width) (target : State width) : Prop :=
  ∀ register (hregister : register < 32),
    target.registers ⟨register, hregister⟩ = source.registers register

theorem wordStackRegisterRelation_writeRegister
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination : Nat) (value : Word width)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination value)
      (writeRegister target ⟨destination, hdestination⟩ value) := by
  intro register hregister
  have htarget := hrel register hregister
  have hdestinationFin : (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  by_cases hsame : register = destination
  · subst register
    simp [wordStackMachineWriteRegister, writeRegister, hdestinationFin]
  · have hfin : (⟨register, hregister⟩ : Fin 32) ≠
        ⟨destination, hdestination⟩ := by
      intro heq
      apply hsame
      exact congrArg Fin.val heq
    simp only [wordStackMachineWriteRegister, writeRegister,
      if_neg hdestinationFin, if_neg hfin, if_neg hsame]
    exact htarget

theorem wordStackRegisterRelation_executeAddi
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination sourceRegister : Nat)
    (immediate : Word width) (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers sourceRegister + immediate))
      (execute target (.addi ⟨destination, hdestination⟩
        ⟨sourceRegister, hsource⟩ immediate)) := by
  have hsourceValue := hrel sourceRegister hsource
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers sourceRegister + immediate))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨sourceRegister, hsource⟩ + immediate))
  rw [hsourceValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers sourceRegister + immediate)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeAdd
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left + source.registers right))
      (execute target (.add ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left + source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ + target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left + source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem wordStackRegisterRelation_executeSub
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left - source.registers right))
      (execute target (.sub ⟨destination, hdestination⟩
        ⟨left, hleft⟩ ⟨right, hright⟩)) := by
  have hleftValue := hrel left hleft
  have hrightValue := hrel right hright
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left - source.registers right))
    (writeRegister {target with pc := nextPc target}
      ⟨destination, hdestination⟩
      (target.registers ⟨left, hleft⟩ - target.registers ⟨right, hright⟩))
  rw [hleftValue, hrightValue]
  apply wordStackRegisterRelation_writeRegister source
    {target with pc := nextPc target} destination
    (source.registers left - source.registers right)
  · intro register hregister
    exact hrel register hregister
  · exact hdestinationNonzero

theorem labCompilePlain_const
    [NeZero width] (destination value : Nat) (hdestination : destination < 32) :
    labCompilePlain (.const destination value : LabPlain (Word width)) =
      some [.addi ⟨destination, hdestination⟩ 0 (BitVec.ofNat width value)] := by
  simp [labCompilePlain, registerOfNat, hdestination]

theorem labCompilePlain_const_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination value : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hdestinationNonzero : destination ≠ 0)
    (hzero : source.registers 0 = 0) :
    (labCompilePlain (.const destination value : LabPlain (Word width))).bind
        (fun code =>
          some (WordStackRegisterRelation
            (wordStackMachineWriteRegister source destination
              (BitVec.ofNat width value))
            (executeInstructions target code))) =
      some (WordStackRegisterRelation
        (wordStackMachineWriteRegister source destination
          (BitVec.ofNat width value))
        (execute target (.addi ⟨destination, hdestination⟩ 0
          (BitVec.ofNat width value)))) := by
  rw [labCompilePlain_const destination value hdestination]
  change some (WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (BitVec.ofNat width value))
    (execute target (.addi ⟨destination, hdestination⟩ 0
      (BitVec.ofNat width value)))) = _
  have hsimulation := wordStackRegisterRelation_executeAddi source target
    destination 0 (BitVec.ofNat width value) hrel hdestination (by omega)
    hdestinationNonzero
  have hzeroAdd : source.registers 0 + BitVec.ofNat width value =
      BitVec.ofNat width value := by
    simpa using congrArg (fun register : Word width =>
      register + BitVec.ofNat width value) hzero
  rw [hzeroAdd] at hsimulation

theorem labCompilePlain_add
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .add destination left right : LabPlain (Word width)) =
      some [.add ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_add_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .add destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left + source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_add (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left + source.registers right))
    (execute target (.add ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeAdd source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

theorem labCompilePlain_sub
    [NeZero width] (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) :
    labCompilePlain (.arith .sub destination left right : LabPlain (Word width)) =
      some [.sub ⟨destination, hdestination⟩ ⟨left, hleft⟩ ⟨right, hright⟩] := by
  simp [labCompilePlain, labBinOpInstruction, registerOfNat,
    hdestination, hleft, hright]
  congr 1

theorem labCompilePlain_sub_register_simulation
    [NeZero width] (source : WordStackMachineState width)
    (target : State width) (destination left right : Nat)
    (hrel : WordStackRegisterRelation source target)
    (hdestination : destination < 32) (hleft : left < 32)
    (hright : right < 32) (hdestinationNonzero : destination ≠ 0)
    (code : List (Instruction width))
    (hcode : labCompilePlain
      (.arith .sub destination left right : LabPlain (Word width)) = some code) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers left - source.registers right))
      (executeInstructions target code) := by
  have hshape := labCompilePlain_sub (width := width) destination left right
    hdestination hleft hright
  rw [hshape] at hcode
  cases hcode
  change WordStackRegisterRelation
    (wordStackMachineWriteRegister source destination
      (source.registers left - source.registers right))
    (execute target (.sub ⟨destination, hdestination⟩
      ⟨left, hleft⟩ ⟨right, hright⟩))
  exact wordStackRegisterRelation_executeSub source target destination left right
    hrel hdestination hleft hright hdestinationNonzero

end Flapjack.RiscV
