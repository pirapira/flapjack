import Flapjack.RiscV.CorrectnessStackRiscV

/-!
# StackRemove current-heap operations at the RISC-V boundary

StackRemove lowers OpCurrHeap to an ordinary register binary operation.
This contract packages the five binary-operation cases behind the
StackRemove-specific source-state update.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveOpCurrHeap [NeZero width]
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
  cases operator with
  | add =>
      exact wordStackRegisterRelation_executeAdd source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | sub =>
      exact wordStackRegisterRelation_executeSub source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | and =>
      exact wordStackRegisterRelation_executeAnd source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | or =>
      exact wordStackRegisterRelation_executeOr source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero
  | xor =>
      exact wordStackRegisterRelation_executeXor source target destination
        sourceRegister config.currHeap hrel hdestination hsource hcurrHeap
        hdestinationNonzero

end Flapjack.RiscV
