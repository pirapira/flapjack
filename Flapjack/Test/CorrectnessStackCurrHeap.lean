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
