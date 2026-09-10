import Flapjack.RiscV.CorrectnessStackDynamicStore
import Flapjack.Test.CorrectnessStackRiscV

/-! Regression tests for dynamic StackRemove frame stores. -/

namespace Flapjack.RiscV

def dynamicStackStoreTestConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

example :
    (executeInstructions (zeroState 64)
        [.or 31 5 5, .add 29 20 6, .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + (zeroState 64).registers 6)
        (stackRiscVTestSource.registers 5)).memory := by
  refine executeStackRemoveStackStoreAny_move_memory
    (config := dynamicStackStoreTestConfig) (source := stackRiscVTestSource)
    (target := zeroState 64) (register := 5) (offsetRegister := 6)
    (hstackPointer := by decide +kernel)
    (haddressScratch := by decide +kernel)
    (hscratchRegister := by decide +kernel)
    (hoffsetRegister := by decide +kernel)
    (hregister := by decide +kernel)
    (hscratchNonzero := by decide +kernel)
    (haddressScratchNonzero := by decide +kernel)
    (hstackPointerScratch := by decide +kernel)
    (hstackPointerAddressScratch := by decide +kernel)
    (hscratchAddressScratch := by decide +kernel)
    (hoffsetRegisterScratch := by decide +kernel)
    (hscratchSource := by decide +kernel)
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])

example :
    (executeInstructions (zeroState 64)
        [.add 29 20 6, .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + (zeroState 64).registers 6)
        (stackRiscVTestSource.registers 31)).memory := by
  refine executeStackRemoveStackStoreAny_same_memory
    (config := dynamicStackStoreTestConfig) (source := stackRiscVTestSource)
    (target := zeroState 64) (register := 31) (offsetRegister := 6)
    (hstackPointer := by decide +kernel)
    (haddressScratch := by decide +kernel)
    (hscratchRegister := by decide +kernel)
    (hoffsetRegister := by decide +kernel)
    (haddressScratchNonzero := by decide +kernel)
    (hstackPointerAddressScratch := by decide +kernel)
    (hscratchAddressScratch := by decide +kernel)
    (hvalue := by simp [stackRiscVTestSource, zeroState])

example :
    compileStackProgramNatToRiscV (width := 64) { services := [] }
      stackRiscVRemoveConfig 2 3 (.stackStoreAny 5 6 : StackProg Nat) =
      some [.or 31 5 5, .add 29 20 6, .storeWord 31 29] := by
  simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
    (compileStackProgramNatToRiscV_stackStoreAny (width := 64)
      { services := [] } stackRiscVRemoveConfig 2 3 5 6
      (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
      (by simp [stackRiscVRemoveConfig]) (by omega) (by omega)
      (by simp [stackRiscVRemoveConfig]))

example :
    (executeInstructions (zeroState 64)
        [.or 31 5 5, .add 29 20 6, .storeWord 31 29]).memory =
      (writeWordValue (zeroState 64)
        ((zeroState 64).registers 20 + (zeroState 64).registers 6)
        (stackRiscVTestSource.registers 5)).memory := by
  apply compileStackProgramNatToRiscV_stackStoreAny_memory
    (context := { services := [] }) (config := stackRiscVRemoveConfig)
    (sectionId := 2) (initialLabel := 3) (register := 5)
    (offsetRegister := 6) (source := stackRiscVTestSource)
    (target := zeroState 64)
    (hstackPointer := by simp [stackRiscVRemoveConfig])
    (haddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchRegister := by simp [stackRiscVRemoveConfig])
    (hoffsetRegister := by omega)
    (hregister := by omega)
    (hscratchNonzero := by simp [stackRiscVRemoveConfig])
    (haddressScratchNonzero := by simp [stackRiscVRemoveConfig])
    (hstackPointerScratch := by simp [stackRiscVRemoveConfig])
    (hstackPointerAddressScratch := by simp [stackRiscVRemoveConfig])
    (hscratchAddressScratch := by simp [stackRiscVRemoveConfig])
    (hoffsetRegisterScratch := by simp [stackRiscVRemoveConfig])
    (hscratchSource := by simp [stackRiscVRemoveConfig])
    (hrel := by
      unfold WordStackRegisterRelationExceptRegister
      intro register hregister hignored
      simp [stackRiscVTestSource, zeroState])
    (code := [.or 31 5 5, .add 29 20 6, .storeWord 31 29])
    (hcode := by
      simpa [stackRiscVRemoveConfig, Fin.ext_iff] using
        (compileStackProgramNatToRiscV_stackStoreAny (width := 64)
          { services := [] } stackRiscVRemoveConfig 2 3 5 6
          (by simp [stackRiscVRemoveConfig]) (by simp [stackRiscVRemoveConfig])
          (by simp [stackRiscVRemoveConfig]) (by omega) (by omega)
          (by simp [stackRiscVRemoveConfig])))

end Flapjack.RiscV
