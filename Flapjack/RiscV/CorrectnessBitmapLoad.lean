import Flapjack.RiscV.CorrectnessStackDelta
import Flapjack.RiscV.CorrectnessStackRemoveBitmap

/-!
# StackRemove bitmap loads at the RISC-V boundary

The bitmap load reads the bitmap-base frame cell, adds the requested bitmap
index, scales that address by the machine word shift, and loads the selected
word.  The contract below states the resulting destination value directly in
the byte-addressed RISC-V memory model.
-/

namespace Flapjack.RiscV

theorem executeStackRemoveBitmapLoad [NeZero width]
    (config : StackRemoveConfig) (target : State width)
    (destination address : Nat)
    (hstoreBase : config.storeBase < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (haddress : address < 32)
    (hscratch : config.scratch < 32)
    (hstoreBaseNonzero : config.storeBase ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hdestinationNonzero : destination ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchStoreBase : config.addressScratch ≠ config.storeBase)
    (hdestinationScratch : destination ≠ config.scratch)
    (haddressDestination : address ≠ destination)
    (haddressAddressScratch : address ≠ config.addressScratch)
    (hzero : target.registers 0 = 0) :
    (executeInstructions target
        [.addi ⟨config.addressScratch, haddressScratch⟩ 0
           (BitVec.ofNat width
             (config.bytesInWord * stackStorePosition .bitmapBase)),
         .sub ⟨config.addressScratch, haddressScratch⟩
           ⟨config.storeBase, hstoreBase⟩
           ⟨config.addressScratch, haddressScratch⟩,
         .loadWord ⟨destination, hdestination⟩
           ⟨config.addressScratch, haddressScratch⟩,
         .add ⟨destination, hdestination⟩
           ⟨destination, hdestination⟩ ⟨address, haddress⟩,
         .addi ⟨config.scratch, hscratch⟩ 0
           (BitVec.ofNat width config.wordShift),
         .sll ⟨destination, hdestination⟩
           ⟨destination, hdestination⟩ ⟨config.scratch, hscratch⟩,
         .loadWord ⟨destination, hdestination⟩
           ⟨destination, hdestination⟩]).registers
        ⟨destination, hdestination⟩ =
      readWordValue target
        ((readWordValue target
            (target.registers ⟨config.storeBase, hstoreBase⟩ -
              BitVec.ofNat width
                (config.bytesInWord * stackStorePosition .bitmapBase)) +
          target.registers ⟨address, haddress⟩) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)) := by
  have hstoreBaseFinNonzero :
      (⟨config.storeBase, hstoreBase⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hstoreBaseNonzero
    exact congrArg Fin.val heq
  have haddressScratchFinNonzero :
      (⟨config.addressScratch, haddressScratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply haddressScratchNonzero
    exact congrArg Fin.val heq
  have hdestinationFinNonzero :
      (⟨destination, hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  have hscratchFinNonzero :
      (⟨config.scratch, hscratch⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hscratchNonzero
    exact congrArg Fin.val heq
  have haddressScratchFinStoreBase :
      (⟨config.addressScratch, haddressScratch⟩ : Fin 32) ≠
        ⟨config.storeBase, hstoreBase⟩ := by
    intro heq
    apply haddressScratchStoreBase
    exact congrArg Fin.val heq
  have hdestinationFinScratch :
      (⟨destination, hdestination⟩ : Fin 32) ≠
        ⟨config.scratch, hscratch⟩ := by
    intro heq
    apply hdestinationScratch
    exact congrArg Fin.val heq
  have haddressFinDestination :
      (⟨address, haddress⟩ : Fin 32) ≠
        ⟨destination, hdestination⟩ := by
    intro heq
    apply haddressDestination
    exact congrArg Fin.val heq
  have haddressFinAddressScratch :
      (⟨address, haddress⟩ : Fin 32) ≠
        ⟨config.addressScratch, haddressScratch⟩ := by
    intro heq
    apply haddressAddressScratch
    exact congrArg Fin.val heq
  let bitmapOffset :=
    BitVec.ofNat width (config.bytesInWord * stackStorePosition .bitmapBase)
  let bitmapAddress :=
    target.registers ⟨config.storeBase, hstoreBase⟩ - bitmapOffset
  have readWordValue_memory (state₁ state₂ : State width)
      (address : Word width) (hmemory : state₁.memory = state₂.memory) :
      readWordValue state₁ address = readWordValue state₂ address := by
    simp [readWordValue, readByte, hmemory]
  let afterImmediate := execute target
    (.addi ⟨config.addressScratch, haddressScratch⟩ 0 bitmapOffset)
  have hafterImmediateAddressScratch :
      afterImmediate.registers ⟨config.addressScratch, haddressScratch⟩ =
        bitmapOffset := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchFinNonzero, hzero]
  have hafterImmediateMemory : afterImmediate.memory = target.memory := by
    simp [afterImmediate, execute, writeRegister, haddressScratchNonzero]
  have hafterImmediateStoreBase :
      afterImmediate.registers ⟨config.storeBase, hstoreBase⟩ =
        target.registers ⟨config.storeBase, hstoreBase⟩ := by
    have hstoreBaseAddressScratch : config.storeBase ≠ config.addressScratch := by
      intro heq
      apply haddressScratchStoreBase
      exact heq.symm
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hstoreBaseAddressScratch, hzero]
  have hafterImmediateZero : afterImmediate.registers 0 = 0 := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchNonzero, hzero]
  have hafterImmediateAddressRegister :
      afterImmediate.registers ⟨address, haddress⟩ =
        target.registers ⟨address, haddress⟩ := by
    simp [afterImmediate, execute, writeRegister, readRegister,
      haddressScratchFinNonzero, haddressFinAddressScratch]
  let afterBase := execute afterImmediate
    (.sub ⟨config.addressScratch, haddressScratch⟩
      ⟨config.storeBase, hstoreBase⟩
      ⟨config.addressScratch, haddressScratch⟩)
  have hafterBaseAddress :
      afterBase.registers ⟨config.addressScratch, haddressScratch⟩ =
        bitmapAddress := by
    simp [afterBase, execute, writeRegister, readRegister,
      haddressScratchFinNonzero,
      hafterImmediateAddressScratch, hafterImmediateStoreBase,
      bitmapAddress]
  have hafterBaseMemory : afterBase.memory = target.memory := by
    simp [afterBase, afterImmediate, execute, writeRegister,
      haddressScratchNonzero]
  have hafterBaseAddressRegister :
      afterBase.registers ⟨address, haddress⟩ =
        target.registers ⟨address, haddress⟩ := by
    have haddressAddressScratch' : address ≠ config.addressScratch := by
      exact haddressAddressScratch
    simp [afterBase, execute, writeRegister, readRegister,
      haddressScratchFinNonzero, haddressFinAddressScratch,
      hafterImmediateAddressRegister, hafterImmediateStoreBase,
      hafterImmediateAddressScratch]
  have hafterBaseZero : afterBase.registers 0 = 0 := by
    simp [afterBase, execute, writeRegister, readRegister,
      haddressScratchNonzero, hafterImmediateZero]
  let afterBitmap := execute afterBase
    (.loadWord ⟨destination, hdestination⟩
      ⟨config.addressScratch, haddressScratch⟩)
  have hafterBitmapDestination :
      afterBitmap.registers ⟨destination, hdestination⟩ =
        readWordValue target bitmapAddress := by
    simp [afterBitmap, execute, writeRegister, readRegister,
      hdestinationFinNonzero, hafterBaseAddress, hafterBaseMemory,
      bitmapAddress,
      readWordValue_memory afterBase target bitmapAddress hafterBaseMemory]
  have hafterBitmapAddress :
      afterBitmap.registers ⟨address, haddress⟩ =
        target.registers ⟨address, haddress⟩ := by
    simp [afterBitmap, execute, writeRegister, readRegister,
      hdestinationFinNonzero, haddressFinDestination,
      hafterBaseAddressRegister]
  have hafterBitmapMemory : afterBitmap.memory = target.memory := by
    simp [afterBitmap, afterBase, afterImmediate, execute, writeRegister,
      hdestinationNonzero, haddressScratchNonzero]
  have hafterBitmapZero : afterBitmap.registers 0 = 0 := by
    simp [afterBitmap, execute, writeRegister, readRegister,
      hdestinationNonzero, hafterBaseZero, hafterBaseMemory]
  let afterAdd := execute afterBitmap
    (.add ⟨destination, hdestination⟩
      ⟨destination, hdestination⟩ ⟨address, haddress⟩)
  have hafterAddDestination :
      afterAdd.registers ⟨destination, hdestination⟩ =
        readWordValue target bitmapAddress +
          target.registers ⟨address, haddress⟩ := by
    simp [afterAdd, execute, writeRegister, readRegister,
      hdestinationFinNonzero, hafterBitmapDestination,
      hafterBitmapAddress]
  have hafterAddMemory : afterAdd.memory = target.memory := by
    simp [afterAdd, afterBitmap, afterBase, afterImmediate,
      execute, writeRegister, hdestinationNonzero, haddressScratchNonzero]
  have hafterAddZero : afterAdd.registers 0 = 0 := by
    simp [afterAdd, execute, writeRegister, readRegister,
      hdestinationFinNonzero, hdestinationNonzero, hafterBitmapZero]
  let afterShiftImmediate := execute afterAdd
    (.addi ⟨config.scratch, hscratch⟩ 0
      (BitVec.ofNat width config.wordShift))
  have hafterShiftImmediateScratch :
      afterShiftImmediate.registers ⟨config.scratch, hscratch⟩ =
        BitVec.ofNat width config.wordShift := by
    simp [afterShiftImmediate, execute, writeRegister, readRegister,
      hscratchFinNonzero, hafterAddZero]
  have hafterShiftImmediateDestination :
      afterShiftImmediate.registers ⟨destination, hdestination⟩ =
        readWordValue target bitmapAddress +
          target.registers ⟨address, haddress⟩ := by
    simp [afterShiftImmediate, execute, writeRegister, readRegister,
      hscratchFinNonzero, hdestinationFinScratch, hafterAddDestination]
  have hafterShiftImmediateMemory :
      afterShiftImmediate.memory = target.memory := by
    simp [afterShiftImmediate, afterAdd, afterBitmap, afterBase,
      afterImmediate, execute, writeRegister, hscratchNonzero,
      hdestinationNonzero, haddressScratchNonzero]
  let afterShift := execute afterShiftImmediate
    (.sll ⟨destination, hdestination⟩
      ⟨destination, hdestination⟩ ⟨config.scratch, hscratch⟩)
  have hafterShiftDestination :
      afterShift.registers ⟨destination, hdestination⟩ =
        BitVec.shiftLeft
          (readWordValue target bitmapAddress +
            target.registers ⟨address, haddress⟩)
          (shiftAmount (BitVec.ofNat width config.wordShift)) := by
    simp [afterShift, execute, writeRegister, readRegister,
      hdestinationFinNonzero, hafterShiftImmediateDestination,
      hafterShiftImmediateScratch]
  have hafterShiftMemory : afterShift.memory = target.memory := by
    simp [afterShift, afterShiftImmediate, afterAdd, afterBitmap,
      afterBase, afterImmediate, execute, writeRegister,
      hdestinationNonzero, hscratchNonzero, haddressScratchNonzero]
  change (execute afterShift
      (.loadWord ⟨destination, hdestination⟩
        ⟨destination, hdestination⟩)).registers
          ⟨destination, hdestination⟩ =
    readWordValue target
      (BitVec.shiftLeft
        (readWordValue target bitmapAddress +
          target.registers ⟨address, haddress⟩)
        (shiftAmount (BitVec.ofNat width config.wordShift)))
  have hreadFinal :
      readWordValue afterShift
          (afterShift.registers ⟨destination, hdestination⟩) =
        readWordValue target
          (BitVec.shiftLeft
            (readWordValue target bitmapAddress +
              target.registers ⟨address, haddress⟩)
            (shiftAmount (BitVec.ofNat width config.wordShift))) := by
    rw [hafterShiftDestination]
    exact readWordValue_memory afterShift target _ hafterShiftMemory
  simp [execute, writeRegister, readRegister, hdestinationNonzero, hreadFinal]

theorem compileStackProgramNatToRiscV_bitmapLoad [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination address : Nat)
    (hstoreBase : config.storeBase < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (haddress : address < 32)
    (hscratch : config.scratch < 32) :
    compileStackProgramNatToRiscV (width := width) context config sectionId initialLabel
      (.bitmapLoad destination address : StackProg Nat) =
      some [
        .addi ⟨config.addressScratch, haddressScratch⟩ 0
          (BitVec.ofNat width
            (config.bytesInWord * stackStorePosition .bitmapBase)),
        .sub ⟨config.addressScratch, haddressScratch⟩
          ⟨config.storeBase, hstoreBase⟩
          ⟨config.addressScratch, haddressScratch⟩,
        .loadWord ⟨destination, hdestination⟩
          ⟨config.addressScratch, haddressScratch⟩,
        .add ⟨destination, hdestination⟩
          ⟨destination, hdestination⟩ ⟨address, haddress⟩,
        .addi ⟨config.scratch, hscratch⟩ 0
          (BitVec.ofNat width config.wordShift),
        .sll ⟨destination, hdestination⟩
          ⟨destination, hdestination⟩ ⟨config.scratch, hscratch⟩,
        .loadWord ⟨destination, hdestination⟩
          ⟨destination, hdestination⟩] := by
  simp [compileStackProgramNatToRiscV, compileLabSectionNat,
    compileLabSection, labProgramToSectionAfterStackRemove, labProgramToSection,
    labFlatten, labSectionNatToWord, labLineNatToWord, labPlainNatToWord,
    labLabel, labCompileLines, labCompilePlain, labCollectLabels,
    labLineInstructionCount, labBinOpInstruction, wordInstToInstruction,
    registerOfNat, labShiftInstructions, hstoreBase, haddressScratch,
    hdestination, haddress, hscratch, stackRemoveBitmapLoad, stackRemoveGet,
    stackRemoveAddress, stackRemoveJoin, stackRemoveComplete, stackProgDepth,
    stackRemoveFuel] <;>
    congr 1

theorem compileStackProgramNatToRiscV_bitmapLoad_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination address : Nat) (target : State width)
    (hstoreBase : config.storeBase < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (haddress : address < 32)
    (hscratch : config.scratch < 32)
    (hstoreBaseNonzero : config.storeBase ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hdestinationNonzero : destination ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchStoreBase : config.addressScratch ≠ config.storeBase)
    (hdestinationScratch : destination ≠ config.scratch)
    (haddressDestination : address ≠ destination)
    (haddressAddressScratch : address ≠ config.addressScratch)
    (hzero : target.registers 0 = 0)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.bitmapLoad destination address : StackProg Nat) =
      some code) :
    (executeInstructions target code).registers
        ⟨destination, hdestination⟩ =
      readWordValue target
        ((readWordValue target
            (target.registers ⟨config.storeBase, hstoreBase⟩ -
              BitVec.ofNat width
                (config.bytesInWord * stackStorePosition .bitmapBase)) +
          target.registers ⟨address, haddress⟩) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)) := by
  rw [compileStackProgramNatToRiscV_bitmapLoad context config sectionId initialLabel
    destination address hstoreBase haddressScratch hdestination haddress hscratch] at hcode
  cases hcode
  exact executeStackRemoveBitmapLoad config target destination address
    hstoreBase haddressScratch hdestination haddress hscratch
    hstoreBaseNonzero haddressScratchNonzero hdestinationNonzero hscratchNonzero
    haddressScratchStoreBase hdestinationScratch haddressDestination
    haddressAddressScratch hzero

theorem compileStackProgramNatToRiscV_bitmapLoad_source_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination address : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstoreBase : config.storeBase < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (haddress : address < 32)
    (hscratch : config.scratch < 32)
    (hstoreBaseNonzero : config.storeBase ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hdestinationNonzero : destination ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchStoreBase : config.addressScratch ≠ config.storeBase)
    (hdestinationScratch : destination ≠ config.scratch)
    (haddressDestination : address ≠ destination)
    (haddressAddressScratch : address ≠ config.addressScratch)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelation source target)
    (hmemory : ∀ address, readWordValue target address = source.memory address)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.bitmapLoad destination address : StackProg Nat) =
      some code) :
    (executeInstructions target code).registers
        ⟨destination, hdestination⟩ =
      source.memory
        ((source.memory
            (source.registers config.storeBase -
              BitVec.ofNat width
                (config.bytesInWord * stackStorePosition .bitmapBase)) +
          source.registers address) <<<
          shiftAmount (BitVec.ofNat width config.wordShift)) := by
  have hcompiled := compileStackProgramNatToRiscV_bitmapLoad_simulation
    (context := context) (config := config) (sectionId := sectionId)
    (initialLabel := initialLabel) (destination := destination)
    (address := address) (target := target)
    (hstoreBase := hstoreBase) (haddressScratch := haddressScratch)
    (hdestination := hdestination) (haddress := haddress) (hscratch := hscratch)
    (hstoreBaseNonzero := hstoreBaseNonzero)
    (haddressScratchNonzero := haddressScratchNonzero)
    (hdestinationNonzero := hdestinationNonzero)
    (hscratchNonzero := hscratchNonzero)
    (haddressScratchStoreBase := haddressScratchStoreBase)
    (hdestinationScratch := hdestinationScratch)
    (haddressDestination := haddressDestination)
    (haddressAddressScratch := haddressAddressScratch) (hzero := hzero)
    (code := code) (hcode := hcode)
  rw [hcompiled]
  simp only [hmemory]
  rw [hrel config.storeBase hstoreBase, hrel address haddress]

theorem compileStackProgramNatToRiscV_bitmapLoad_eval_simulation [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel destination address : Nat)
    (source : WordStackMachineState width) (target : State width)
    (hstoreBase : config.storeBase < 32)
    (haddressScratch : config.addressScratch < 32)
    (hdestination : destination < 32)
    (haddress : address < 32)
    (hscratch : config.scratch < 32)
    (hstoreBaseNonzero : config.storeBase ≠ 0)
    (haddressScratchNonzero : config.addressScratch ≠ 0)
    (hdestinationNonzero : destination ≠ 0)
    (hscratchNonzero : config.scratch ≠ 0)
    (haddressScratchStoreBase : config.addressScratch ≠ config.storeBase)
    (hdestinationScratch : destination ≠ config.scratch)
    (haddressDestination : address ≠ destination)
    (haddressAddressScratch : address ≠ config.addressScratch)
    (hzero : target.registers 0 = 0)
    (hrel : WordStackRegisterRelation source target)
    (hmemory : ∀ address, readWordValue target address = source.memory address)
    (code : List (Instruction width))
    (hcode : compileStackProgramNatToRiscV (width := width) context config
      sectionId initialLabel (.bitmapLoad destination address : StackProg Nat) =
      some code) :
    (evalWordStackMachine source
      (stackRemoveBitmapLoad config destination address)).map
        (fun final => final.registers destination) =
      some ((executeInstructions target code).registers
        ⟨destination, hdestination⟩) := by
  rw [evalStackRemoveBitmapLoad config source destination address
    haddressScratchStoreBase hdestinationScratch haddressDestination
    haddressAddressScratch]
  congr 1
  symm
  exact compileStackProgramNatToRiscV_bitmapLoad_source_simulation
    context config sectionId initialLabel destination address source target
    hstoreBase haddressScratch hdestination haddress hscratch
    hstoreBaseNonzero haddressScratchNonzero hdestinationNonzero hscratchNonzero
    haddressScratchStoreBase hdestinationScratch haddressDestination
    haddressAddressScratch hzero hrel hmemory code hcode

end Flapjack.RiscV
