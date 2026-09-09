import Flapjack.RiscV.CorrectnessStackOpCurrHeap

/-! Regression interface for the generic StackRemove current-heap contract. -/

namespace Flapjack.RiscV

example [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (operator : BinOp)
    (destination sourceRegister : Nat)
    (hcurrHeap : config.currHeap < 32)
    (hdestination : destination < 32)
    (hsource : sourceRegister < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hrel : WordStackRegisterRelation source target) :
    WordStackRegisterRelation
      (wordStackMachineWriteRegister source destination
        (wordStackMachineBinOp operator
          (source.registers sourceRegister)
          (source.registers config.currHeap)))
      (executeInstructions target
        (match operator with
        | .add =>
            [.add ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .sub =>
            [.sub ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .and =>
            [.and ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .or =>
            [.or ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩]
        | .xor =>
            [.xor ⟨destination, hdestination⟩
              ⟨sourceRegister, hsource⟩ ⟨config.currHeap, hcurrHeap⟩])) := by
  exact executeStackRemoveOpCurrHeap config source target operator
    destination sourceRegister hcurrHeap hdestination hsource
    hdestinationNonzero hrel

end Flapjack.RiscV
