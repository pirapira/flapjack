import Flapjack.RiscV.CorrectnessStackMemory

/-!
# StackRemove frame-cell stores at the RISC-V boundary

This is the store companion to CorrectnessStackMemory: the copy into the
scratch register, address calculation, and storeWord sequence has exactly
the byte-memory effect of writing the source word to the frame cell.
-/

namespace Flapjack.RiscV

theorem foldWriteBytes_memory [NeZero width]
    (state₁ state₂ : State width) (address value : Word width)
    (offsets : List Nat) (hmemory : state₁.memory = state₂.memory) :
    (offsets.foldl
      (fun state offset =>
        writeByte state (byteAddress address offset)
          (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) state₁).memory =
      (offsets.foldl
        (fun state offset =>
          writeByte state (byteAddress address offset)
            (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) state₂).memory := by
  induction offsets generalizing state₁ state₂ with
  | nil => exact hmemory
  | cons offset offsets ih =>
      simp only [List.foldl]
      apply ih
      simp [writeByte, hmemory]

theorem writeRegister_memory (state : State width) (register : Fin 32)
    (value : Word width) :
    (writeRegister state register value).memory = state.memory := by
  unfold writeRegister
  split <;> rfl

theorem executeStackRemoveStackStore_move_memory [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (register offset : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hregister : register < 32)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hscratchAddressScratch : config.scratch ≠ config.addressScratch)
    (hscratchSource : config.scratch ≠ register)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target) :
    (executeInstructions target
        [.or ⟨config.scratch, hscratchRegister⟩
          ⟨register, hregister⟩ ⟨register, hregister⟩,
         .addi ⟨config.addressScratch, haddressScratch⟩ 0
           (BitVec.ofNat width (config.bytesInWord * offset)),
         .add ⟨config.addressScratch, haddressScratch⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨config.addressScratch, haddressScratch⟩,
         .storeWord ⟨config.scratch, hscratchRegister⟩
           ⟨config.addressScratch, haddressScratch⟩]).memory =
      (writeWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          BitVec.ofNat width (config.bytesInWord * offset))
        (source.registers register)).memory := by
  have hregisterFinScratch :
      (⟨register, hregister⟩ : Fin 32) ≠
        ⟨config.scratch, hscratchRegister⟩ := by
    intro heq
    apply hscratchSource
    exact (congrArg Fin.val heq).symm
  have hstackPointerFinScratch :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠
        ⟨config.scratch, hscratchRegister⟩ := by
    intro heq
    apply hstackPointerScratch
    exact congrArg Fin.val heq
  have hstackPointerFinAddressScratch :
      (⟨config.stackPointer, hstackPointer⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hstackPointerAddressScratch
    exact congrArg Fin.val heq
  have hscratchFinAddressScratch :
      (⟨config.scratch, hscratchRegister⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply hscratchAddressScratch
    exact congrArg Fin.val heq
  have haddressScratchFinNonzero :
      (⟨config.addressScratch, haddressScratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply haddressScratchNonzero
    exact congrArg Fin.val heq
  have hregisterSource : register ≠ config.scratch := by
    intro heq
    apply hscratchSource
    exact heq.symm
  have htargetRegister := hrel register hregister hregisterSource
  let afterMove := execute target
    (.or ⟨config.scratch, hscratchRegister⟩
      ⟨register, hregister⟩ ⟨register, hregister⟩)
  have hafterMoveScratch :
      afterMove.registers ⟨config.scratch, hscratchRegister⟩ =
        source.registers register := by
    simp [afterMove, execute, writeRegister, readRegister,
      hscratchNonzero, htargetRegister]
  have hafterMoveStackPointer :
      afterMove.registers ⟨config.stackPointer, hstackPointer⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ := by
    simp [afterMove, execute, writeRegister, readRegister,
      hscratchNonzero, hstackPointerFinScratch]
  have hafterMoveZero : afterMove.registers 0 = 0 := by
    simp [afterMove, execute, writeRegister, hscratchNonzero, hzero]
  have hafterMoveMemory : afterMove.memory = target.memory := by
    simp [afterMove, execute, writeRegister, hscratchNonzero]
  let afterImmediate := execute afterMove
    (.addi ⟨config.addressScratch, haddressScratch⟩ 0
      (BitVec.ofNat width (config.bytesInWord * offset)))
  have hafterImmediateScratch :
      afterImmediate.registers ⟨config.addressScratch, haddressScratch⟩ =
        BitVec.ofNat width (config.bytesInWord * offset) := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hafterMoveZero]
  have hafterImmediateValue :
      afterImmediate.registers ⟨config.scratch, hscratchRegister⟩ =
        source.registers register := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hscratchFinAddressScratch,
      hafterMoveScratch]
  have hafterImmediateStackPointer :
      afterImmediate.registers ⟨config.stackPointer, hstackPointer⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hstackPointerFinAddressScratch,
      hafterMoveStackPointer, hafterMoveZero]
  have hafterImmediateMemory : afterImmediate.memory = target.memory := by
    calc
      afterImmediate.memory = afterMove.memory := by
        simpa [afterImmediate, execute] using
          writeRegister_memory
            ({ afterMove with pc := nextPc afterMove })
            ⟨config.addressScratch, haddressScratch⟩
            (readRegister afterMove 0 +
              BitVec.ofNat width (config.bytesInWord * offset))
      _ = target.memory := hafterMoveMemory
  let afterAddress := execute afterImmediate
    (.add ⟨config.addressScratch, haddressScratch⟩
      ⟨config.stackPointer, hstackPointer⟩
      ⟨config.addressScratch, haddressScratch⟩)
  have hafterAddressScratch :
      afterAddress.registers ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          BitVec.ofNat width (config.bytesInWord * offset) := by
    simp [afterAddress, execute, writeRegister, readRegister,
      haddressScratchNonzero, hafterImmediateScratch,
      hafterImmediateStackPointer]
  have hafterAddressMemory : afterAddress.memory = target.memory := by
    calc
      afterAddress.memory = afterImmediate.memory := by
        simpa [afterAddress, execute] using
          writeRegister_memory
            ({ afterImmediate with pc := nextPc afterImmediate })
            ⟨config.addressScratch, haddressScratch⟩
            (readRegister afterImmediate ⟨config.stackPointer, hstackPointer⟩ +
              readRegister afterImmediate ⟨config.addressScratch, haddressScratch⟩)
      _ = target.memory := hafterImmediateMemory
  have hstoreAddress :
      readRegister afterAddress
          ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          BitVec.ofNat width (config.bytesInWord * offset) := by
    exact hafterAddressScratch
  have hstoreValue :
      readRegister afterAddress ⟨config.scratch, hscratchRegister⟩ =
        source.registers register := by
    simp [readRegister, afterAddress, execute, writeRegister,
      haddressScratchNonzero, hscratchFinAddressScratch,
      hafterImmediateValue]
  change (execute afterAddress
      (.storeWord ⟨config.scratch, hscratchRegister⟩
        ⟨config.addressScratch, haddressScratch⟩)).memory =
    (writeWordValue target
      (target.registers ⟨config.stackPointer, hstackPointer⟩ +
        BitVec.ofNat width (config.bytesInWord * offset))
      (source.registers register)).memory
  change (writeWordValue
      { afterAddress with pc := nextPc afterAddress }
      (readRegister afterAddress ⟨config.addressScratch, haddressScratch⟩)
      (readRegister afterAddress ⟨config.scratch, hscratchRegister⟩)).memory =
    (writeWordValue target
      (target.registers ⟨config.stackPointer, hstackPointer⟩ +
        BitVec.ofNat width (config.bytesInWord * offset))
      (source.registers register)).memory
  rw [hstoreAddress, hstoreValue]
  apply foldWriteBytes_memory
  simp [hafterAddressMemory]

end Flapjack.RiscV
