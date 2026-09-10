import Flapjack.RiscV.CorrectnessStackOpCurrHeap

/-! Regression interface for the generic StackRemove current-heap contract. -/

namespace Flapjack.RiscV

def stackOpCurrHeapTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example (operator : BinOp) :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackOpCurrHeapTestConfig 2 3 (.opCurrHeap operator 5 6 : StackProg Nat) =
      some [match operator with
        | .add => .add 5 6 12
        | .sub => .sub 5 6 12
        | .and => .and 5 6 12
        | .or => .or 5 6 12
        | .xor => .xor 5 6 12] := by
  cases operator <;>
    simpa [stackOpCurrHeapTestConfig, Fin.ext_iff] using
      (compileStackProgramNatToRiscV_opCurrHeap (width := 64)
        { services := [] } stackOpCurrHeapTestConfig _ 2 3 5 6
        (by decide +kernel) (by decide +kernel) (by decide +kernel))

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
