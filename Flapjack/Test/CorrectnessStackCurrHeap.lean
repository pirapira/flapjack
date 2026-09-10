import Flapjack.RiscV.CorrectnessStackCurrHeap

/-! Regression interface for current-heap StackRemove get/set contracts. -/

namespace Flapjack.RiscV

def stackCurrHeapTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

def stackCurrHeapTestSource : WordStackMachineState 64 :=
  { registers := fun _ => 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackCurrHeapTestConfig 2 3 (.get 5 .currHeap : StackProg Nat) =
      some [.or 5 12 12] := by
  simpa [stackCurrHeapTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_getCurrHeap (width := 64)
      { services := [] } stackCurrHeapTestConfig 2 3 5
      (by decide +kernel) (by decide +kernel))

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackCurrHeapTestConfig 2 3 (.set .currHeap 6 : StackProg Nat) =
      some [.or 12 6 6] := by
  simpa [stackCurrHeapTestConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_setCurrHeap (width := 64)
      { services := [] } stackCurrHeapTestConfig 2 3 6
      (by decide +kernel) (by decide +kernel))

example :
    (evalWordStackMachine stackCurrHeapTestSource
      (stackRemoveGet stackCurrHeapTestConfig 5 .currHeap)).map
        (fun final => final.registers 5) =
      some ((executeInstructions (zeroState 64) [.or 5 12 12]).registers 5) := by
  apply compileStackProgramNatToRiscV_getCurrHeap_eval_simulation
    (context := { services := [] }) (config := stackCurrHeapTestConfig)
    (sectionId := 2) (initialLabel := 3) (destination := 5)
    (source := stackCurrHeapTestSource) (target := zeroState 64)
    (hcurrHeap := by decide +kernel)
    (hdestination := by decide +kernel)
    (hdestinationNonzero := by decide +kernel)
    (hrel := by
      intro register hregister
      simp [stackCurrHeapTestSource, zeroState])
    (code := [.or 5 12 12])
    (hcode := by
      simpa [stackCurrHeapTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_getCurrHeap (width := 64)
          { services := [] } stackCurrHeapTestConfig 2 3 5
          (by decide +kernel) (by decide +kernel)))

example :
    (evalWordStackMachine stackCurrHeapTestSource
      (stackRemoveSet stackCurrHeapTestConfig .currHeap 6)).map
        (fun final => final.registers stackCurrHeapTestConfig.currHeap) =
      some ((executeInstructions (zeroState 64) [.or 12 6 6]).registers
        ⟨stackCurrHeapTestConfig.currHeap, by decide +kernel⟩) := by
  apply compileStackProgramNatToRiscV_setCurrHeap_eval_simulation
    (context := { services := [] }) (config := stackCurrHeapTestConfig)
    (sectionId := 2) (initialLabel := 3) (sourceRegister := 6)
    (source := stackCurrHeapTestSource) (target := zeroState 64)
    (hcurrHeap := by decide +kernel)
    (hsource := by decide +kernel)
    (hcurrHeapNonzero := by decide +kernel)
    (hrel := by
      intro register hregister
      simp [stackCurrHeapTestSource, zeroState])
    (code := [.or 12 6 6])
    (hcode := by
      simpa [stackCurrHeapTestConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_setCurrHeap (width := 64)
          { services := [] } stackCurrHeapTestConfig 2 3 6
          (by decide +kernel) (by decide +kernel)))

example [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (destination : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (source.registers config.currHeap))
      (executeInstructions target
        [.or ⟨destination, hdestination⟩
          ⟨config.currHeap, hcurrHeap⟩ ⟨config.currHeap, hcurrHeap⟩]) := by
  exact executeStackRemoveGetCurrHeap config source target destination
    hcurrHeap hdestination hdestinationNonzero hrel

example [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hsource : sourceRegister < 32)
    (hcurrHeapNonzero : config.currHeap ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source config.currHeap
        (source.registers sourceRegister))
      (executeInstructions target
        [.or ⟨config.currHeap, hcurrHeap⟩
          ⟨sourceRegister, hsource⟩ ⟨sourceRegister, hsource⟩]) := by
  exact executeStackRemoveSetCurrHeap config source target sourceRegister
    hcurrHeap hsource hcurrHeapNonzero hrel

end Flapjack.RiscV
