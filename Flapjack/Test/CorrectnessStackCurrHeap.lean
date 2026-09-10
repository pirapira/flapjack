import Flapjack.RiscV.CorrectnessStackCurrHeap

/-! Regression interface for current-heap StackRemove get/set contracts. -/

namespace Flapjack.RiscV

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
