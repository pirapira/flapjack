import Flapjack.RiscV.CorrectnessStackStore
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression test for the StackRemove stack-store memory contract. -/

namespace Flapjack.RiscV

example :
    (executeInstructions (zeroState 64)
        [.or 31 5 5,
         .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + BitVec.ofNat 64 (8 * 12))
        (stackRiscVTestSource.registers 5)).memory := by
  let config : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 20
      bytesInWord := 8
      stackBase := 21
      wordShift := 3 }
  refine executeStackRemoveStackStore_move_memory
    (config := config) (source := stackRiscVTestSource)
    (target := zeroState 64) (register := 5) (offset := 12)
    (hstackPointer := by dsimp [config]; decide +kernel)
    (haddressScratch := by dsimp [config]; decide +kernel)
    (hscratchRegister := by dsimp [config]; decide +kernel)
    (hregister := by decide +kernel)
    (hscratchNonzero := by dsimp [config]; decide +kernel)
    (haddressScratchNonzero := by dsimp [config]; decide +kernel)
    (hstackPointerScratch := by dsimp [config]; decide +kernel)
    (hstackPointerAddressScratch := by dsimp [config]; decide +kernel)
    (hscratchAddressScratch := by dsimp [config]; decide +kernel)
    (hscratchSource := by dsimp [config]; decide +kernel)
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVRemoveConfig 2 3 (.stackStore 5 12 : StackProg Nat) =
      some [.or 31 5 5, .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
        .add 29 20 29, .storeWord 31 29] := by
  simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackStore (width := 64)
      { services := [] } stackRiscVRemoveConfig 2 3 5 12
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
      (by simp [stackRiscVRemoveConfig]) (by omega)
      (by simp [stackRiscVRemoveConfig]))

example :
    (executeInstructions (zeroState 64)
        [.or 31 5 5,
         .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + BitVec.ofNat 64 (8 * 12))
        (stackRiscVTestSource.registers 5)).memory := by
  apply compileStackProgramNatToRiscV_stackStore_memory
    (context := { services := [] }) (config := stackRiscVRemoveConfig)
    (sectionId := 2) (initialLabel := 3) (register := 5) (offset := 12)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by simp [stackRiscVRemoveConfig])
    (haddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchRegister := by simp [stackRiscVRemoveConfig])
    (hregister := by omega)
    (hscratchNonzero := by simp [stackRiscVRemoveConfig])
    (haddressScratchNonzero := by simp [stackRiscVRemoveConfig])
    (hstackPointerScratch := by simp [stackRiscVRemoveConfig])
    (hstackPointerAddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchAddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchSource := by simp [stackRiscVRemoveConfig])
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (code := [.or 31 5 5, .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
      .add 29 20 29, .storeWord 31 29])
        (hcode := by
      simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackStore (width := 64)
          { services := [] } stackRiscVRemoveConfig 2 3 5 12
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by simp [stackRiscVRemoveConfig]) (by omega)
          (by simp [stackRiscVRemoveConfig])))

example :
    (evalWordStackMachine stackRiscVTestSource
      (stackRemoveStackStore stackRiscVRemoveConfig 5 12)).map
        (fun final => final.memory
          (stackRiscVTestSource.registers stackRiscVRemoveConfig.stackPointer +
            BitVec.ofNat 64 (stackRiscVRemoveConfig.bytesInWord * 12))) =
      some (readWordValue (executeInstructions (zeroState 64)
        [.or 31 5 5,
         .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
         .add 29 20 29,
         .storeWord 31 29])
        ((zeroState 64).registers 20 + BitVec.ofNat 64 (8 * 12))) := by
  apply compileStackProgramNatToRiscV_stackStore_eval_simulation
    (context := { services := [] }) (config := stackRiscVRemoveConfig)
    (sectionId := 2) (initialLabel := 3) (register := 5) (offset := 12)
    (source := stackRiscVTestSource) (target := zeroState 64)
    (hstackPointer := by simp [stackRiscVRemoveConfig])
    (haddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchRegister := by simp [stackRiscVRemoveConfig])
    (hregister := by omega)
    (hscratchNonzero := by simp [stackRiscVRemoveConfig])
    (haddressScratchNonzero := by simp [stackRiscVRemoveConfig])
    (hstackPointerScratch := by simp [stackRiscVRemoveConfig])
    (hstackPointerAddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchAddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchSource := by simp [stackRiscVRemoveConfig])
    (hzero := by simp [zeroState])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (hread := by
      decide +kernel)
    (code := [.or 31 5 5,
      .addi 29 0 (BitVec.ofNat 64 (8 * 12)),
      .add 29 20 29,
      .storeWord 31 29])
    (hcode := by
      simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackStore (width := 64)
          { services := [] } stackRiscVRemoveConfig 2 3 5 12
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by simp [stackRiscVRemoveConfig]) (by omega)
          (by simp [stackRiscVRemoveConfig])))

end Flapjack.RiscV
