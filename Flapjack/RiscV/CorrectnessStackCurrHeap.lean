import Flapjack.RiscV.CorrectnessStackOpCurrHeap

/-!
# StackRemove current-heap get/set at the RISC-V boundary

The current-heap fast paths are ordinary or instructions: a get copies the
configured current-heap register, while a set writes the source value back to
that register.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveGetCurrHeap [NeZero width]
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
  simpa [executeInstructions, wordStackMachineBinOp] using
    wordStackRegisterRelation_executeOr source target destination
    config.currHeap config.currHeap hrel hdestination hcurrHeap hcurrHeap
    hdestinationNonzero

theorem executeStackRemoveSetCurrHeap [NeZero width]
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
  simpa [executeInstructions, wordStackMachineBinOp] using
    wordStackRegisterRelation_executeOr source target config.currHeap
    sourceRegister sourceRegister hrel hcurrHeap hsource hsource
    hcurrHeapNonzero

end Flapjack.RiscV
