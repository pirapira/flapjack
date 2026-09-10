import Flapjack.RiscV.CorrectnessStackMemory
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression test for the StackRemove-to-RISC-V byte-memory boundary. -/

namespace Flapjack.RiscV

example :
    WordStackRegisterRelationExceptRegister 29
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.stack 12))
      (executeInstructions (zeroState 64)
        [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .loadWord 5 29]) := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackLoad
    (config := config)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (destination := 5) (offset := 12)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (haddressScratch := by dsimp [config]; decide +kernel)
    (hdestination := by decide +kernel)
    (hdestinationNonzero := by decide +kernel)
    (haddressScratchNonzero := by dsimp [config]; decide +kernel)
    (hstackPointerScratch := by dsimp [config]; decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (hcell := by
      unfold WordStackStackCellRelation
      simp [stackRiscVTestSource, zeroState, readWordValue, readByte, byteAddress]
      decide +kernel)

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVRemoveConfig 2 3 (.stackLoad 5 12 : StackProg Nat) =
      some [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
        .add 29 20 29, .loadWord 5 29] := by
  simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackLoad (width := 64)
      { services := [] } stackRiscVRemoveConfig 2 3 5 12
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
      (by omega))

example :
    WordStackRegisterRelationExceptRegister 29
      (wordStackMachineWriteRegister stackRiscVTestSource 5
        (stackRiscVTestSource.stack 12))
      (executeInstructions (zeroState 64)
        [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29, .loadWord 5 29]) := by
  apply compileStackProgramNatToRiscV_stackLoad_simulation
    (context := { services := [] }) (config := stackRiscVRemoveConfig)
    (sectionId := 2) (initialLabel := 3) (destination := 5) (offset := 12)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by simp [stackRiscVRemoveConfig])
    (haddressScratch := by simp [stackRiscVRemoveConfig])
    (hdestination := by omega) (hdestinationNonzero := by omega)
    (haddressScratchNonzero := by simp [stackRiscVRemoveConfig])
    (hstackPointerScratch := by simp [stackRiscVRemoveConfig])
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (hcell := by
      unfold WordStackStackCellRelation
      simp [stackRiscVTestSource, zeroState, readWordValue, readByte, byteAddress]
      decide +kernel)
    (code := [.addi 29 0 (BitVec.ofNat 64 (8 * 12)),
      .add 29 20 29, .loadWord 5 29])
    (hcode := by
      simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackLoad (width := 64)
          { services := [] } stackRiscVRemoveConfig 2 3 5 12
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by omega)))

end Flapjack.RiscV
