import Flapjack.RiscV.CorrectnessStackStore
import Flapjack.RiscV.CorrectnessStackRemoveDynamic

/-!
# Dynamic StackRemove frame-cell stores at the RISC-V boundary

The dynamic store uses a register-held byte offset.  The non-aliasing theorem
below records the register condition required by the lowering: the offset
register must survive the source-to-scratch copy.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveStackStoreAny_move_memory [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (register offsetRegister : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hregister : register < 32)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hscratchAddressScratch : config.scratch ≠ config.addressScratch)
    (hoffsetRegisterScratch : offsetRegister ≠ config.scratch)
    (hscratchSource : config.scratch ≠ register)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target) :
    (executeInstructions target
        [.or ⟨config.scratch, hscratchRegister⟩
          ⟨register, hregister⟩ ⟨register, hregister⟩,
         .add ⟨config.addressScratch, haddressScratch⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨offsetRegister, hoffsetRegister⟩,
         .storeWord ⟨config.scratch, hscratchRegister⟩
           ⟨config.addressScratch, haddressScratch⟩]).memory =
      (writeWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)
        (source.registers register)).memory := by
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
  have hoffsetRegisterFinScratch :
      (⟨offsetRegister, hoffsetRegister⟩ : Fin 32) ≠
        ⟨config.scratch, hscratchRegister⟩ := by
    intro heq
    apply hoffsetRegisterScratch
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
  have hafterMoveOffsetRegister :
      afterMove.registers ⟨offsetRegister, hoffsetRegister⟩ =
        target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    simp [afterMove, execute, writeRegister, readRegister,
      hscratchNonzero, hoffsetRegisterFinScratch]
  have hafterMoveMemory : afterMove.memory = target.memory := by
    simp [afterMove, execute, writeRegister, hscratchNonzero]
  let afterAddress := execute afterMove
    (.add ⟨config.addressScratch, haddressScratch⟩
      ⟨config.stackPointer, hstackPointer⟩
      ⟨offsetRegister, hoffsetRegister⟩)
  have hafterAddressScratch :
      afterAddress.registers ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    simp [afterAddress, execute, writeRegister, readRegister,
      haddressScratchFinNonzero,
      hafterMoveStackPointer, hafterMoveOffsetRegister]
  have hafterAddressMemory : afterAddress.memory = target.memory := by
    calc
      afterAddress.memory = afterMove.memory := by
        simpa [afterAddress, execute, readRegister] using
          writeRegister_memory
            ({ afterMove with pc := nextPc afterMove })
            ⟨config.addressScratch, haddressScratch⟩
            (readRegister afterMove ⟨config.stackPointer, hstackPointer⟩ +
              readRegister afterMove ⟨offsetRegister, hoffsetRegister⟩)
      _ = target.memory := hafterMoveMemory
  have hstoreAddress :
      readRegister afterAddress
          ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    exact hafterAddressScratch
  have hstoreValue :
      readRegister afterAddress ⟨config.scratch, hscratchRegister⟩ =
        source.registers register := by
    simp [readRegister, afterAddress, execute, writeRegister,
      haddressScratchFinNonzero, hscratchFinAddressScratch,
      hafterMoveScratch]
  change (execute afterAddress
      (.storeWord ⟨config.scratch, hscratchRegister⟩
        ⟨config.addressScratch, haddressScratch⟩)).memory =
    (writeWordValue target
      (target.registers ⟨config.stackPointer, hstackPointer⟩ +
        target.registers ⟨offsetRegister, hoffsetRegister⟩)
      (source.registers register)).memory
  apply executeStoreWord_memory
  · exact hstoreAddress
  · exact hstoreValue
  · exact hafterAddressMemory

theorem executeStackRemoveStackStoreAny_same_memory [NeZero width]
    (config : StackRemoveConfig) (source : WordStackMachineState width)
    (target : State width) (register offsetRegister : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hscratchAddressScratch : config.scratch ≠ config.addressScratch)
    (hvalue :
      target.registers ⟨config.scratch, hscratchRegister⟩ =
        source.registers register) :
    (executeInstructions target
        [.add ⟨config.addressScratch, haddressScratch⟩
           ⟨config.stackPointer, hstackPointer⟩
           ⟨offsetRegister, hoffsetRegister⟩,
         .storeWord ⟨config.scratch, hscratchRegister⟩
           ⟨config.addressScratch, haddressScratch⟩]).memory =
      (writeWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)
        (source.registers register)).memory := by
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
  let afterAddress := execute target
    (.add ⟨config.addressScratch, haddressScratch⟩
      ⟨config.stackPointer, hstackPointer⟩
      ⟨offsetRegister, hoffsetRegister⟩)
  have hafterAddressScratch :
      afterAddress.registers ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    simp [afterAddress, execute, writeRegister, readRegister,
      haddressScratchFinNonzero]
  have hafterAddressMemory : afterAddress.memory = target.memory := by
    simpa [afterAddress, execute, readRegister] using
      writeRegister_memory
        ({ target with pc := nextPc target })
        ⟨config.addressScratch, haddressScratch⟩
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)
  have hstoreAddress :
      readRegister afterAddress
          ⟨config.addressScratch, haddressScratch⟩ =
        target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩ := by
    exact hafterAddressScratch
  have hstoreValue :
      readRegister afterAddress ⟨config.scratch, hscratchRegister⟩ =
        source.registers register := by
    simp [readRegister, afterAddress, execute, writeRegister,
      haddressScratchFinNonzero, hscratchFinAddressScratch, hvalue]
  change (execute afterAddress
      (.storeWord ⟨config.scratch, hscratchRegister⟩
        ⟨config.addressScratch, haddressScratch⟩)).memory =
    (writeWordValue target
      (target.registers ⟨config.stackPointer, hstackPointer⟩ +
        target.registers ⟨offsetRegister, hoffsetRegister⟩)
      (source.registers register)).memory
  apply executeStoreWord_memory
  · exact hstoreAddress
  · exact hstoreValue
  · exact hafterAddressMemory

theorem compileStackProgramNatToRiscV_stackStoreAny [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register offsetRegister : Nat)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hregister : register < 32)
    (hscratchSource : config.scratch ≠ register) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.stackStoreAny register offsetRegister : StackProg Nat) =
      some [.or ⟨config.scratch, hscratchRegister⟩
          ⟨register, hregister⟩ ⟨register, hregister⟩,
        .add ⟨config.addressScratch, haddressScratch⟩
          ⟨config.stackPointer, hstackPointer⟩
          ⟨offsetRegister, hoffsetRegister⟩,
        .storeWord ⟨config.scratch, hscratchRegister⟩
          ⟨config.addressScratch, haddressScratch⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, labBinOpInstruction, wordInstToInstruction,
    registerOfNat, hstackPointer, haddressScratch, hscratchRegister,
    hoffsetRegister, hregister, hscratchSource, stackRemoveStackStoreAny,
    stackRemoveMove, stackRemoveJoin, stackRemoveComplete, stackProgDepth,
    stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_stackStoreAny_memory [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register offsetRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hregister : register < 32)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hscratchAddressScratch : config.scratch ≠ config.addressScratch)
    (hoffsetRegisterScratch : offsetRegister ≠ config.scratch)
    (hscratchSource : config.scratch ≠ register)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackStoreAny register offsetRegister : StackProg Nat) =
      some code) :
    (executeInstructions target code).memory =
      (writeWordValue target
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)
        (source.registers register)).memory := by
  rw [compileStackProgramNatToRiscV_stackStoreAny context config sectionId initialLabel
    register offsetRegister hstackPointer haddressScratch hscratchRegister
    hoffsetRegister hregister hscratchSource] at hcode
  cases hcode
  exact executeStackRemoveStackStoreAny_move_memory config source target register
    offsetRegister hstackPointer haddressScratch hscratchRegister hoffsetRegister
    hregister hscratchNonzero haddressScratchNonzero hstackPointerScratch
    hstackPointerAddressScratch hscratchAddressScratch hoffsetRegisterScratch
    hscratchSource hrel

theorem compileStackProgramNatToRiscV_stackStoreAny_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel register offsetRegister : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstackPointer : config.stackPointer < 32)
    (haddressScratch : config.addressScratch < 32)
    (hscratchRegister : config.scratch < 32)
    (hoffsetRegister : offsetRegister < 32)
    (hregister : register < 32)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hstackPointerScratch : config.stackPointer ≠ config.scratch)
    (hstackPointerAddressScratch : config.stackPointer ≠ config.addressScratch)
    (hscratchAddressScratch : config.scratch ≠ config.addressScratch)
    (hoffsetRegisterScratch : offsetRegister ≠ config.scratch)
    (hscratchSource : config.scratch ≠ register)
    (hrel : WordStackRegisterRelationExceptRegister config.scratch source target)
    (hread : readWordValue
        (writeWordValue target
          (target.registers ⟨config.stackPointer, hstackPointer⟩ +
            target.registers ⟨offsetRegister, hoffsetRegister⟩)
          (source.registers register))
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩) =
      source.registers register)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.stackStoreAny register offsetRegister : StackProg Nat) =
      some code) :
    (evalWordStackMachine source
      (stackRemoveStackStoreAny config register offsetRegister)).map
        (fun final => final.memory
          (source.registers config.stackPointer + source.registers offsetRegister)) =
      some (readWordValue (executeInstructions target code)
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩)) := by
  rw [evalStackRemoveStackStoreAny config source register offsetRegister
    hscratchAddressScratch hstackPointerScratch.symm
    hoffsetRegisterScratch.symm]
  congr 1
  have hmemory := compileStackProgramNatToRiscV_stackStoreAny_memory
    context config sectionId initialLabel register offsetRegister source target
    hstackPointer haddressScratch hscratchRegister hoffsetRegister hregister
    hscratchNonzero haddressScratchNonzero hstackPointerScratch
    hstackPointerAddressScratch hscratchAddressScratch hoffsetRegisterScratch
    hscratchSource hrel code hcode
  have hreadMemory (state₁ state₂ : State width) (address : Word width)
      (hmemory : state₁.memory = state₂.memory) :
      readWordValue state₁ address = readWordValue state₂ address := by
    simp [readWordValue, readByte, hmemory]
  symm
  calc
    readWordValue (executeInstructions target code)
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩) =
      readWordValue
        (writeWordValue target
          (target.registers ⟨config.stackPointer, hstackPointer⟩ +
            target.registers ⟨offsetRegister, hoffsetRegister⟩)
          (source.registers register))
        (target.registers ⟨config.stackPointer, hstackPointer⟩ +
          target.registers ⟨offsetRegister, hoffsetRegister⟩) := by
      exact hreadMemory _ _ _ hmemory
    _ = source.registers register := by
      exact hread

end Flapjack.RiscV
