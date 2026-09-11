import Flapjack.RiscV.AllocatorCorrectness

/-!
Semantic facts for the SSA-renaming stage of the Word allocator.

The CakeML reference renames every read through the current SSA map while
leaving a store's state and fresh-name counter unchanged.  This file starts
the corresponding executable proof boundary; subsequent instruction cases can
be added without unfolding the graph allocator.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordSsaRenameInst_store
    (ssa : WordSsaState) (source address : Nat) :
    wordSsaRenameInst ssa (.mem .store source address : WordInst) =
      (ssa, .mem .store (wordSsaRead ssa source) (wordSsaRead ssa address)) := by
  rfl

theorem wordSsaRead_fresh_name (state : WordSsaState) (name : Nat) :
    wordSsaRead (wordSsaFresh state name).1 name = state.next := by
  simp [wordSsaRead, wordSsaFresh, lookupNatInfo]

theorem wordSsaRead_fresh_of_ne (state : WordSsaState) (name other : Nat)
    (hneq : other ≠ name) :
    wordSsaRead (wordSsaFresh state name).1 other = wordSsaRead state other := by
  have hlookup : ∀ entries : NatInfoMap Nat,
      lookupNatInfo other (entries.filter (fun entry => entry.1 != name)) =
        lookupNatInfo other entries := by
    intro entries
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rcases entry with ⟨key, value⟩
        by_cases hkeyName : key = name
        · subst key
          simp [lookupNatInfo, ih, Ne.symm hneq]
        · simp [lookupNatInfo, ih, hkeyName]
  simp only [wordSsaRead, wordSsaFresh]
  have hhead : lookupNatInfo other
      ((name, state.next) :: state.current.filter (fun entry => entry.1 != name)) =
      lookupNatInfo other (state.current.filter (fun entry => entry.1 != name)) := by
    simp [lookupNatInfo, Ne.symm hneq]
  rw [hhead, hlookup state.current]

theorem wordSsaRenameInst_load
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameInst ssa (.mem .load destination address : WordInst) =
      ((wordSsaFresh ssa destination).1,
        .mem .load (wordSsaFresh ssa destination).2
          (wordSsaRead ssa address)) := by
  rfl

theorem writeWordValue_memory_congr [NeZero width]
    (left right : State width) (address value : Word width)
    (hmemory : left.memory = right.memory) :
    (writeWordValue left address value).memory =
      (writeWordValue right address value).memory := by
  let offsets := List.range (width / 8)
  change (offsets.foldl (fun state offset =>
    writeByte state (byteAddress address offset)
      (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) left).memory =
    (offsets.foldl (fun state offset =>
      writeByte state (byteAddress address offset)
        (BitVec.ofNat 8 (value.toNat / 256 ^ offset % 256))) right).memory
  induction offsets generalizing left right with
  | nil => exact hmemory
  | cons offset offsets ih =>
      simp only [List.foldl]
      apply ih
      simp [writeByte, hmemory]

theorem evalWordProg_ssaRename_store [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (sourceName address : Nat)
    (hsource : sourceName < 32) (haddress : address < 32)
    (hsourceSsa : wordSsaRead ssa sourceName < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.inst (.mem .store sourceName address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (.inst (wordSsaRenameInst ssa
          (.mem .store sourceName address : WordInst)).2)).map
        (fun state => state.memory) := by
  have hsourceValue :
      readRegister source ⟨sourceName, hsource⟩ =
        readRegister target ⟨wordSsaRead ssa sourceName, hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [registerOfNat, hsource, hsourceSsa] using h
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  rw [wordSsaRenameInst_store]
  simp [evalWordProg, registerOfNat, hsource, haddress, hsourceSsa,
    haddressSsa, hsourceValue, haddressValue, hmemory, execute]
  apply writeWordValue_memory_congr
  rfl

theorem writeByte_memory_congr
    (left right : State width) (address : Word width) (value : BitVec 8)
    (hmemory : left.memory = right.memory) :
    (writeByte left address value).memory =
      (writeByte right address value).memory := by
  simp [writeByte, hmemory]

theorem writeWord16_memory_congr
    (left right : State width) (address value : Word width)
    (hmemory : left.memory = right.memory) :
    (writeWord16 left address value).memory =
      (writeWord16 right address value).memory := by
  simp [writeWord16, writeByte, byteAddress, hmemory]

theorem writeWord32_memory_congr
    (left right : State width) (address value : Word width)
    (hmemory : left.memory = right.memory) :
    (writeWord32 left address value).memory =
      (writeWord32 right address value).memory := by
  simp [writeWord32, writeByte, byteAddress, hmemory]

theorem evalWordProg_ssaRename_store_family [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (operator : WordMemOp) (sourceName address : Nat)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hsource : sourceName < 32) (haddress : address < 32)
    (hsourceSsa : wordSsaRead ssa sourceName < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.inst (.mem operator sourceName address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (.inst (wordSsaRenameInst ssa
          (.mem operator sourceName address : WordInst)).2)).map
        (fun state => state.memory) := by
  have hsourceValue :
      readRegister source ⟨sourceName, hsource⟩ =
        readRegister target ⟨wordSsaRead ssa sourceName, hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [registerOfNat, hsource, hsourceSsa] using h
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  rcases hoperator with rfl | rfl | rfl | rfl
  · exact evalWordProg_ssaRename_store ssa source target hregister hmemory
      sourceName address hsource haddress hsourceSsa haddressSsa
  · simp [wordSsaRenameInst, evalWordProg, registerOfNat, hsource, haddress,
      hsourceSsa, haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeByte_memory_congr
    rfl
  · simp [wordSsaRenameInst, evalWordProg, registerOfNat, hsource, haddress,
      hsourceSsa, haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeWord16_memory_congr
    rfl
  · simp [wordSsaRenameInst, evalWordProg, registerOfNat, hsource, haddress,
      hsourceSsa, haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeWord32_memory_congr
    rfl

theorem evalWordProg_ssaRename_load_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  have hloadValue :
      readWordValue source (readRegister source ⟨address, haddress⟩) =
        readWordValue target
          (readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWordValue, readByte, hmemory]
  rw [wordSsaRenameInst_load]
  refine ⟨execute source (.loadWord ⟨destination, hdestination⟩
      ⟨address, haddress⟩),
    execute target (.loadWord ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa address, haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, registerOfNat, hdestination, haddress, execute]
  · simp [evalWordProg, registerOfNat, hfresh, haddressSsa, execute]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load8_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load8 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load8 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  have hloadValue :
      BitVec.ofNat width
          (readByte source (readRegister source ⟨address, haddress⟩)).toNat =
        BitVec.ofNat width
          (readByte target
            (readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩)).toNat := by
    rw [haddressValue]
    simp [readByte, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.loadByte ⟨destination, hdestination⟩
      ⟨address, haddress⟩),
    execute target (.loadByte ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa address, haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, registerOfNat, hdestination, haddress, execute]
  · simp [evalWordProg, registerOfNat, hfresh, haddressSsa, execute]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load16_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load16 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load16 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  have hloadValue :
      readWord16 source (readRegister source ⟨address, haddress⟩) =
        readWord16 target
          (readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord16, readByte, byteAddress, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.loadHalf ⟨destination, hdestination⟩
      ⟨address, haddress⟩),
    execute target (.loadHalf ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa address, haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, registerOfNat, hdestination, haddress, execute]
  · simp [evalWordProg, registerOfNat, hfresh, haddressSsa, execute]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load32_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load32 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load32 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨address, haddress⟩ =
        readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩ := by
    have h := hregister address
    simpa [registerOfNat, haddress, haddressSsa] using h
  have hloadValue :
      readWord32 source (readRegister source ⟨address, haddress⟩) =
        readWord32 target
          (readRegister target ⟨wordSsaRead ssa address, haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord32, readByte, byteAddress, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.load32 ⟨destination, hdestination⟩
      ⟨address, haddress⟩),
    execute target (.load32 ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa address, haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, registerOfNat, hdestination, haddress, execute]
  · simp [evalWordProg, registerOfNat, hfresh, haddressSsa, execute]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_locValue
    (ssa : WordSsaState) (destination label : Nat) :
    wordSsaRenameProgram ssa (.locValue destination label : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .locValue (wordSsaFresh ssa destination).2 label) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops]

theorem evalWordProg_ssaRename_locValue_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzero : readRegister source 0 = readRegister target 0)
    (destination label : Nat)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.locValue destination label) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa (.locValue destination label)).2 =
        some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  rw [wordSsaRenameProgram_locValue]
  have hzero' : source.registers 0 = target.registers 0 := by
    simpa [readRegister] using hzero
  refine ⟨execute source (.addi ⟨destination, hdestination⟩ 0
      (BitVec.ofNat width label)),
    execute target (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩ 0
      (BitVec.ofNat width label)), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordLocValueToInstructions, executeInstructions,
      registerOfNat, hdestination]
  · simp [evalWordProg, wordLocValueToInstructions, executeInstructions,
      registerOfNat, hfresh]
  · simp [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero, hzero']
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_var
    (ssa : WordSsaState) (destination source : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.var source) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa source))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_var_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination sourceName : Nat)
    (hdestination : destination < 32) (hsource : sourceName < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hsourceSsa : wordSsaRead ssa sourceName < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.assign destination (.var sourceName)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.var sourceName))).2 = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister source ⟨sourceName, hsource⟩ =
        readRegister target ⟨wordSsaRead ssa sourceName, hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [registerOfNat, hsource, hsourceSsa] using h
  rw [wordSsaRenameProgram_assign_var]
  refine ⟨execute source (.addi ⟨destination, hdestination⟩
      ⟨sourceName, hsource⟩ 0),
    execute target (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa sourceName, hsourceSsa⟩ 0), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hdestination, hsource, executeInstructions]
  · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hfresh, hsourceSsa, executeInstructions]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hsourceValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_const
    (ssa : WordSsaState) (destination : Nat) (value : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.const value) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2 (.const value)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_const_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzero : readRegister source 0 = readRegister target 0)
    (destination : Nat) (value : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.assign destination (.const value)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.const value))).2 = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  rw [wordSsaRenameProgram_assign_const]
  have hzero' : source.registers 0 = target.registers 0 := by
    simpa [readRegister] using hzero
  refine ⟨execute source (.addi ⟨destination, hdestination⟩ 0 value),
    execute target (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩ 0 value),
    ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hdestination, executeInstructions]
  · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hfresh, executeInstructions]
  · simp [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero, hzero']
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_binary_var_var
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.var left, .var right]) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.var (wordSsaRead ssa left), .var (wordSsaRead ssa right)])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_binary_var_var_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination left right : Nat) (operator : BinOp)
    (hdestination : destination < 32) (hleft : left < 32) (hright : right < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hleftSsa : wordSsaRead ssa left < 32)
    (hrightSsa : wordSsaRead ssa right < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source
          (.assign destination (.op operator [.var left, .var right])) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.var left, .var right]))).2 = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hleftValue :
      readRegister source ⟨left, hleft⟩ =
        readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ := by
    have h := hregister left
    simpa [registerOfNat, hleft, hleftSsa] using h
  have hrightValue :
      readRegister source ⟨right, hright⟩ =
        readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
    have h := hregister right
    simpa [registerOfNat, hright, hrightSsa] using h
  rw [wordSsaRenameProgram_assign_binary_var_var]
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩ =
            readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ +
              readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.add ⟨destination, hdestination⟩
          ⟨left, hleft⟩ ⟨right, hright⟩),
        execute target (.add ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa left, hleftSsa⟩
          ⟨wordSsaRead ssa right, hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hleft, hright, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hleftSsa, hrightSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | sub =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩ =
            readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ -
              readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.sub ⟨destination, hdestination⟩
          ⟨left, hleft⟩ ⟨right, hright⟩),
        execute target (.sub ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa left, hleftSsa⟩
          ⟨wordSsaRead ssa right, hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hleft, hright, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hleftSsa, hrightSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | and =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩ =
            readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ &&&
              readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.and ⟨destination, hdestination⟩
          ⟨left, hleft⟩ ⟨right, hright⟩),
        execute target (.and ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa left, hleftSsa⟩
          ⟨wordSsaRead ssa right, hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hleft, hright, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hleftSsa, hrightSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | or =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩ =
            readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ |||
              readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.or ⟨destination, hdestination⟩
          ⟨left, hleft⟩ ⟨right, hright⟩),
        execute target (.or ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa left, hleftSsa⟩
          ⟨wordSsaRead ssa right, hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hleft, hright, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hleftSsa, hrightSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | xor =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩ =
            readRegister target ⟨wordSsaRead ssa left, hleftSsa⟩ ^^^
              readRegister target ⟨wordSsaRead ssa right, hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.xor ⟨destination, hdestination⟩
          ⟨left, hleft⟩ ⟨right, hright⟩),
        execute target (.xor ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa left, hleftSsa⟩
          ⟨wordSsaRead ssa right, hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hleft, hright, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hleftSsa, hrightSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_binary_var_const
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (source : Nat) (value : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.var source, .const value]) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.var (wordSsaRead ssa source), .const value])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_binary_var_const_destination [NeZero width]
    (ssa : WordSsaState) (sourceState targetState : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination source : Nat) (operator : BinOp) (value : Word width)
    (hdestination : destination < 32) (hsource : source < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hsourceSsa : wordSsaRead ssa source < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.op operator [.var source, .const value])) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.var source, .const value]))).2 =
        some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister sourceState ⟨source, hsource⟩ =
        readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ := by
    have h := hregister source
    simpa [registerOfNat, hsource, hsourceSsa] using h
  rw [wordSsaRenameProgram_assign_binary_var_const]
  cases operator with
  | add =>
      have hvalue :
          readRegister sourceState ⟨source, hsource⟩ + value =
            readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ + value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.addi ⟨destination, hdestination⟩
          ⟨source, hsource⟩ value),
        execute targetState (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa source, hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hsource, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hsourceSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | sub =>
      have hvalue :
          readRegister sourceState ⟨source, hsource⟩ - value =
            readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ - value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.addi ⟨destination, hdestination⟩
          ⟨source, hsource⟩ (0 - value)),
        execute targetState (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa source, hsourceSsa⟩ (0 - value)), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hsource, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hsourceSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | and =>
      have hvalue :
          readRegister sourceState ⟨source, hsource⟩ &&& value =
            readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ &&& value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.andi ⟨destination, hdestination⟩
          ⟨source, hsource⟩ value),
        execute targetState (.andi ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa source, hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hsource, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hsourceSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | or =>
      have hvalue :
          readRegister sourceState ⟨source, hsource⟩ ||| value =
            readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ ||| value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.ori ⟨destination, hdestination⟩
          ⟨source, hsource⟩ value),
        execute targetState (.ori ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa source, hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hsource, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hsourceSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | xor =>
      have hvalue :
          readRegister sourceState ⟨source, hsource⟩ ^^^ value =
            readRegister targetState ⟨wordSsaRead ssa source, hsourceSsa⟩ ^^^ value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.xori ⟨destination, hdestination⟩
          ⟨source, hsource⟩ value),
        execute targetState (.xori ⟨(wordSsaFresh ssa destination).2, hfresh⟩
          ⟨wordSsaRead ssa source, hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hdestination, hsource, executeInstructions]
      · simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hfresh, hsourceSsa, executeInstructions]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_binary_const_const
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (left right : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.const left, .const right]) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.const left, .const right])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_binary_const_const_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzero : readRegister source 0 = readRegister target 0)
    (destination : Nat) (operator : BinOp) (left right : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source
          (.assign destination (.op operator [.const left, .const right])) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.const left, .const right]))).2 =
        some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  let result : Word width := match operator with
    | .add => left + right
    | .sub => left - right
    | .and => left &&& right
    | .or => left ||| right
    | .xor => left ^^^ right
  rw [wordSsaRenameProgram_assign_binary_const_const]
  have hzero' : source.registers 0 = target.registers 0 := by
    simpa [readRegister] using hzero
  refine ⟨execute source (.addi ⟨destination, hdestination⟩ 0 result),
    execute target (.addi ⟨(wordSsaFresh ssa destination).2, hfresh⟩ 0 result),
    ?_, ?_, ?_, ?_⟩
  · cases operator <;>
      simp [result, evalWordProg, wordExpToInstructions,
        wordExpToInstruction, registerOfNat, hdestination, executeInstructions]
  · cases operator <;>
      simp [result, evalWordProg, wordExpToInstructions,
        wordExpToInstruction, registerOfNat, hfresh, executeInstructions]
  · simp [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero, hzero']
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameInst_div
    (ssa : WordSsaState) (destination dividend divisor : Nat) :
    wordSsaRenameInst ssa (.arith (.div destination dividend divisor) : WordInst) =
      ((wordSsaFresh ssa destination).1,
        .arith (.div (wordSsaFresh ssa destination).2
          (wordSsaRead ssa dividend) (wordSsaRead ssa divisor))) := by
  rfl

theorem evalWordProg_ssaRename_div_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination dividend divisor : Nat)
    (hdestination : destination < 32) (hdividend : dividend < 32)
    (hdivisor : divisor < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hdividendSsa : wordSsaRead ssa dividend < 32)
    (hdivisorSsa : wordSsaRead ssa divisor < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : (wordSsaFresh ssa destination).2 ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.arith (.div destination dividend divisor))) =
          some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.arith (.div destination dividend divisor) : WordInst)).2) =
          some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨(wordSsaFresh ssa destination).2, hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hdividendValue :
      readRegister source ⟨dividend, hdividend⟩ =
        readRegister target ⟨wordSsaRead ssa dividend, hdividendSsa⟩ := by
    have h := hregister dividend
    simpa [registerOfNat, hdividend, hdividendSsa] using h
  have hdivisorValue :
      readRegister source ⟨divisor, hdivisor⟩ =
        readRegister target ⟨wordSsaRead ssa divisor, hdivisorSsa⟩ := by
    have h := hregister divisor
    simpa [registerOfNat, hdivisor, hdivisorSsa] using h
  rw [wordSsaRenameInst_div]
  refine ⟨execute source (.divU ⟨destination, hdestination⟩
      ⟨dividend, hdividend⟩ ⟨divisor, hdivisor⟩),
    execute target (.divU ⟨(wordSsaFresh ssa destination).2, hfresh⟩
      ⟨wordSsaRead ssa dividend, hdividendSsa⟩
      ⟨wordSsaRead ssa divisor, hdivisorSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
      registerOfNat, hdestination, hdividend, hdivisor, executeInstructions]
  · simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
      registerOfNat, hfresh, hdividendSsa, hdivisorSsa, executeInstructions]
  · rw [execute_divU, execute_divU]
    simp [hdestinationNonzero, hfreshNonzero, hdividendValue, hdivisorValue]
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameInst_longMul
    (ssa : WordSsaState) (destinationLeft destinationRight sourceLeft sourceRight : Nat) :
    wordSsaRenameInst ssa
        (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : WordInst) =
      (let sourceLeft := wordSsaRead ssa sourceLeft
       let sourceRight := wordSsaRead ssa sourceRight
       let (ssa, freshLeft) := wordSsaFresh ssa destinationLeft
       let (ssa, freshRight) := wordSsaFresh ssa destinationRight
       (ssa, .arith (.longMul freshLeft freshRight
         sourceLeft sourceRight))) := by
  rfl

theorem evalWordProg_ssaRename_longMul_destinations [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (first second : WordSsaState) (freshLeft freshRight : Nat)
    (destinationLeft destinationRight sourceLeft sourceRight : Nat)
    (hfirst : wordSsaFresh ssa destinationLeft = (first, freshLeft))
    (hsecond : wordSsaFresh first destinationRight = (second, freshRight))
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hdestinationLeft : destinationLeft < 32)
    (hdestinationRight : destinationRight < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hdestinationLeftNonzero : destinationLeft ≠ 0)
    (hdestinationRightNonzero : destinationRight ≠ 0)
    (hdestinationDistinct : destinationLeft ≠ destinationRight)
    (hdestinationLeftSourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeftSourceRight : destinationLeft ≠ sourceRight)
    (hsourceLeftSsa : wordSsaRead ssa sourceLeft < 32)
    (hsourceRightSsa : wordSsaRead ssa sourceRight < 32)
    (hfreshLeftBound : freshLeft < 32) (hfreshRightBound : freshRight < 32)
    (hfreshLeftNonzero : freshLeft ≠ 0) (hfreshRightNonzero : freshRight ≠ 0)
    (hfreshDistinct : freshLeft ≠ freshRight)
    (hfreshLeftSourceLeft : freshLeft ≠ wordSsaRead ssa sourceLeft)
    (hfreshLeftSourceRight : freshLeft ≠ wordSsaRead ssa sourceRight) :
    ∃ source' target',
      evalWordProg source
          (.inst (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight))) =
          some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : WordInst)).2) =
          some target' ∧
      readRegister source' ⟨destinationLeft, hdestinationLeft⟩ =
        readRegister target' ⟨freshLeft, hfreshLeftBound⟩ ∧
      readRegister source' ⟨destinationRight, hdestinationRight⟩ =
        readRegister target' ⟨freshRight, hfreshRightBound⟩ ∧
      source'.memory = target'.memory := by
  have hsourceLeftValue :
      readRegister source ⟨sourceLeft, hsourceLeft⟩ =
        readRegister target ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩ := by
    have h := hregister sourceLeft
    simpa [registerOfNat, hsourceLeft, hsourceLeftSsa] using h
  have hsourceRightValue :
      readRegister source ⟨sourceRight, hsourceRight⟩ =
        readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩ := by
    have h := hregister sourceRight
    simpa [registerOfNat, hsourceRight, hsourceRightSsa] using h
  rw [wordSsaRenameInst]
  simp only [hfirst, hsecond]
  have hdestinationLeftNonzero' :
      (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠ 0 := by
    simp [hdestinationLeftNonzero]
  have hdestinationRightNonzero' :
      (⟨destinationRight, hdestinationRight⟩ : Fin 32) ≠ 0 := by
    simp [hdestinationRightNonzero]
  have hfreshLeftNonzero' :
      (⟨freshLeft, hfreshLeftBound⟩ : Fin 32) ≠ 0 := by
    simp [hfreshLeftNonzero]
  have hfreshRightNonzero' :
      (⟨freshRight, hfreshRightBound⟩ : Fin 32) ≠ 0 := by
    simp [hfreshRightNonzero]
  have hdestinationDistinct' :
      (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
        ⟨destinationRight, hdestinationRight⟩ := by
    simp [hdestinationDistinct]
  have hfreshDistinct' :
      (⟨freshLeft, hfreshLeftBound⟩ : Fin 32) ≠
        ⟨freshRight, hfreshRightBound⟩ := by
    simp [hfreshDistinct]
  have hdestinationLeftSourceLeft' :
      (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
        ⟨sourceLeft, hsourceLeft⟩ := by
    simp [hdestinationLeftSourceLeft]
  have hdestinationLeftSourceRight' :
      (⟨destinationLeft, hdestinationLeft⟩ : Fin 32) ≠
        ⟨sourceRight, hsourceRight⟩ := by
    simp [hdestinationLeftSourceRight]
  have hfreshLeftSourceLeft' :
      (⟨freshLeft, hfreshLeftBound⟩ : Fin 32) ≠
        ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩ := by
    simp [hfreshLeftSourceLeft]
  have hfreshLeftSourceRight' :
      (⟨freshLeft, hfreshLeftBound⟩ : Fin 32) ≠
        ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩ := by
    simp [hfreshLeftSourceRight]
  refine ⟨executeInstructions source
      [.mulHU ⟨destinationLeft, hdestinationLeft⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
       .mul ⟨destinationRight, hdestinationRight⟩
          ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩],
    executeInstructions target
      [.mulHU ⟨freshLeft, hfreshLeftBound⟩
          ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
          ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
       .mul ⟨freshRight, hfreshRightBound⟩
          ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
          ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩], ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordArithToInstructions, registerOfNat,
      hdestinationLeft, hdestinationRight, hsourceLeft, hsourceRight,
      hdestinationLeftSourceLeft, hdestinationLeftSourceRight,
      executeInstructions]
  · simp [evalWordProg, wordArithToInstructions, registerOfNat,
      hfreshLeftBound, hfreshRightBound, hsourceLeftSsa, hsourceRightSsa,
      hfreshLeftSourceLeft, hfreshLeftSourceRight, executeInstructions]
  · have hresult := executeInstructions_longMul_general source
        ⟨destinationLeft, hdestinationLeft⟩ ⟨destinationRight, hdestinationRight⟩
        ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩
        hdestinationLeftNonzero' hdestinationRightNonzero'
        hdestinationDistinct' hdestinationLeftSourceLeft'
        hdestinationLeftSourceRight'
    have hleft := congrArg Prod.fst hresult
    have htarget := executeInstructions_longMul_general target
        ⟨freshLeft, hfreshLeftBound⟩ ⟨freshRight, hfreshRightBound⟩
        ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
        ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩
        hfreshLeftNonzero' hfreshRightNonzero' hfreshDistinct'
        hfreshLeftSourceLeft' hfreshLeftSourceRight'
    have htargetLeft := congrArg Prod.fst htarget
    calc
      readRegister (executeInstructions source
        [.mulHU ⟨destinationLeft, hdestinationLeft⟩
            ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
         .mul ⟨destinationRight, hdestinationRight⟩
            ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩])
          ⟨destinationLeft, hdestinationLeft⟩ = _ := hleft
      _ = BitVec.ofNat width
          ((readRegister target ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩).toNat *
            (readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩).toNat /
            2 ^ width) := by rw [hsourceLeftValue, hsourceRightValue]
      _ = readRegister (executeInstructions target
        [.mulHU ⟨freshLeft, hfreshLeftBound⟩
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
            ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
         .mul ⟨freshRight, hfreshRightBound⟩
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
            ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩])
          ⟨freshLeft, hfreshLeftBound⟩ := htargetLeft.symm
  · have hresult := executeInstructions_longMul_general source
        ⟨destinationLeft, hdestinationLeft⟩ ⟨destinationRight, hdestinationRight⟩
        ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩
        hdestinationLeftNonzero' hdestinationRightNonzero'
        hdestinationDistinct' hdestinationLeftSourceLeft'
        hdestinationLeftSourceRight'
    have hright := congrArg Prod.snd hresult
    have htarget := executeInstructions_longMul_general target
        ⟨freshLeft, hfreshLeftBound⟩ ⟨freshRight, hfreshRightBound⟩
        ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
        ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩
        hfreshLeftNonzero' hfreshRightNonzero' hfreshDistinct'
        hfreshLeftSourceLeft' hfreshLeftSourceRight'
    have htargetRight := congrArg Prod.snd htarget
    calc
      readRegister (executeInstructions source
        [.mulHU ⟨destinationLeft, hdestinationLeft⟩
            ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
         .mul ⟨destinationRight, hdestinationRight⟩
            ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩])
          ⟨destinationRight, hdestinationRight⟩ = _ := hright
      _ = readRegister target ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩ *
          readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩ := by
            rw [hsourceLeftValue, hsourceRightValue]
      _ = readRegister (executeInstructions target
        [.mulHU ⟨freshLeft, hfreshLeftBound⟩
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
            ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
         .mul ⟨freshRight, hfreshRightBound⟩
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
            ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩])
          ⟨freshRight, hfreshRightBound⟩ := htargetRight.symm
  · have hsourceMemory :
        (executeInstructions source
          [.mulHU ⟨destinationLeft, hdestinationLeft⟩
              ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
           .mul ⟨destinationRight, hdestinationRight⟩
              ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩]).memory =
          source.memory := by
      simp [executeInstructions, execute, writeRegister,
        hdestinationLeftNonzero, hdestinationRightNonzero]
    have htargetMemory :
        (executeInstructions target
          [.mulHU ⟨freshLeft, hfreshLeftBound⟩
              ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
              ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
           .mul ⟨freshRight, hfreshRightBound⟩
              ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
              ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩]).memory =
          target.memory := by
      simp [executeInstructions, execute, writeRegister,
        hfreshLeftNonzero, hfreshRightNonzero]
    exact hsourceMemory.trans (hmemory.trans htargetMemory.symm)

theorem evalWordProg_ssaRename_addCarry_destinations [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (first second : WordSsaState) (freshDestination freshCarry : Nat)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (hfirst : wordSsaFresh ssa destination = (first, freshDestination))
    (hsecond : wordSsaFresh first resultCarry = (second, freshCarry))
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hdestination : destination < 32) (hresultCarry : resultCarry < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hcarryIn : carryIn < 32)
    (hsourceZero : readRegister source 0 = 0)
    (htargetZero : readRegister target 0 = 0)
    (hdestinationNonzero : destination ≠ 0)
    (hresultCarryNonzero : resultCarry ≠ 0)
    (hdestinationDistinct : destination ≠ resultCarry)
    (hdestinationSourceRight : destination ≠ sourceRight)
    (hdestinationScratch : destination ≠ 31)
    (hresultCarryScratch : resultCarry ≠ 31)
    (hsourceLeftScratch : sourceLeft ≠ 31)
    (hsourceRightScratch : sourceRight ≠ 31)
    (hcarryInScratch : carryIn ≠ 31)
    (hsourceLeftSsa : wordSsaRead ssa sourceLeft < 32)
    (hsourceRightSsa : wordSsaRead ssa sourceRight < 32)
    (hcarryInSsa : wordSsaRead ssa carryIn < 32)
    (hfreshDestinationBound : freshDestination < 32)
    (hfreshCarryBound : freshCarry < 32)
    (hfreshDestinationNonzero : freshDestination ≠ 0)
    (hfreshCarryNonzero : freshCarry ≠ 0)
    (hfreshDistinct : freshDestination ≠ freshCarry)
    (hfreshDestinationSourceRight :
      freshDestination ≠ wordSsaRead ssa sourceRight)
    (hfreshDestinationScratch : freshDestination ≠ 31)
    (hfreshCarryScratch : freshCarry ≠ 31)
    (hfreshSourceLeftScratch : wordSsaRead ssa sourceLeft ≠ 31)
    (hfreshSourceRightScratch : wordSsaRead ssa sourceRight ≠ 31)
    (hfreshCarryInScratch : wordSsaRead ssa carryIn ≠ 31) :
    ∃ source' target',
      evalWordProg source
          (.inst (.arith (.addCarry destination resultCarry
            sourceLeft sourceRight carryIn))) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.arith (.addCarry destination resultCarry
              sourceLeft sourceRight carryIn) : WordInst)).2) = some target' ∧
      readRegister source' ⟨destination, hdestination⟩ =
        readRegister target' ⟨freshDestination, hfreshDestinationBound⟩ ∧
      readRegister source' ⟨resultCarry, hresultCarry⟩ =
        readRegister target' ⟨freshCarry, hfreshCarryBound⟩ ∧
      source'.memory = target'.memory := by
  have hsourceLeftValue :
      readRegister source ⟨sourceLeft, hsourceLeft⟩ =
        readRegister target ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩ := by
    have h := hregister sourceLeft
    simpa [registerOfNat, hsourceLeft, hsourceLeftSsa] using h
  have hsourceRightValue :
      readRegister source ⟨sourceRight, hsourceRight⟩ =
        readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩ := by
    have h := hregister sourceRight
    simpa [registerOfNat, hsourceRight, hsourceRightSsa] using h
  have hcarryInValue :
      readRegister source ⟨carryIn, hcarryIn⟩ =
        readRegister target ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩ := by
    have h := hregister carryIn
    simpa [registerOfNat, hcarryIn, hcarryInSsa] using h
  rw [wordSsaRenameInst]
  simp only [hfirst, hsecond]
  let sourceCode : List (Instruction width) :=
    [.sltu 31 0 ⟨carryIn, hcarryIn⟩,
     .add ⟨destination, hdestination⟩
       ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩,
     .sltu ⟨resultCarry, hresultCarry⟩
       ⟨destination, hdestination⟩ ⟨sourceRight, hsourceRight⟩,
     .add ⟨destination, hdestination⟩
       ⟨destination, hdestination⟩ 31,
     .sltu 31 ⟨destination, hdestination⟩ 31,
     .or ⟨resultCarry, hresultCarry⟩
       ⟨resultCarry, hresultCarry⟩ 31]
  let targetCode : List (Instruction width) :=
    [.sltu 31 0 ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩,
     .add ⟨freshDestination, hfreshDestinationBound⟩
       ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
       ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
     .sltu ⟨freshCarry, hfreshCarryBound⟩
       ⟨freshDestination, hfreshDestinationBound⟩
       ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩,
     .add ⟨freshDestination, hfreshDestinationBound⟩
       ⟨freshDestination, hfreshDestinationBound⟩ 31,
     .sltu 31 ⟨freshDestination, hfreshDestinationBound⟩ 31,
     .or ⟨freshCarry, hfreshCarryBound⟩
       ⟨freshCarry, hfreshCarryBound⟩ 31]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, wordArithToInstructions,
      registerOfNat, hdestination, hresultCarry, hsourceLeft, hsourceRight,
      hcarryIn, hdestinationScratch, hresultCarryScratch,
      hsourceLeftScratch, hsourceRightScratch, hcarryInScratch,
      executeInstructions]
  · simp [targetCode, evalWordProg, wordArithToInstructions,
      registerOfNat, hfreshDestinationBound, hfreshCarryBound,
      hsourceLeftSsa, hsourceRightSsa, hcarryInSsa,
      hfreshDestinationScratch, hfreshCarryScratch,
      hfreshSourceLeftScratch, hfreshSourceRightScratch,
      hfreshCarryInScratch, executeInstructions]
  · have hsource := executeInstructions_addCarry_general source
        ⟨destination, hdestination⟩ ⟨resultCarry, hresultCarry⟩
        ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩
        ⟨carryIn, hcarryIn⟩ hsourceZero
        (by intro heq; apply hdestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationDistinct; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationSourceRight; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hsourceLeftScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hsourceRightScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hcarryInScratch; exact congrArg Fin.val heq)
    have htarget := executeInstructions_addCarry_general target
        ⟨freshDestination, hfreshDestinationBound⟩
        ⟨freshCarry, hfreshCarryBound⟩
        ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
        ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩
        ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩ htargetZero
        (by intro heq; apply hfreshDestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDistinct; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDestinationSourceRight; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDestinationScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshSourceLeftScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshSourceRightScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryInScratch; exact congrArg Fin.val heq)
    have hsourceLeftResult := congrArg Prod.fst hsource
    have htargetLeftResult := congrArg Prod.fst htarget
    calc
      readRegister (executeInstructions source sourceCode)
          ⟨destination, hdestination⟩ =
          (addCarryWords (readRegister source ⟨sourceLeft, hsourceLeft⟩)
            (readRegister source ⟨sourceRight, hsourceRight⟩)
            (readRegister source ⟨carryIn, hcarryIn⟩)).1 := by
              exact hsourceLeftResult
      _ = (addCarryWords (readRegister target
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩)
            (readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩)
            (readRegister target ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩)).1 := by
              rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
      _ = readRegister (executeInstructions target targetCode)
          ⟨freshDestination, hfreshDestinationBound⟩ := by
              exact htargetLeftResult.symm
  · have hsource := executeInstructions_addCarry_general source
        ⟨destination, hdestination⟩ ⟨resultCarry, hresultCarry⟩
        ⟨sourceLeft, hsourceLeft⟩ ⟨sourceRight, hsourceRight⟩
        ⟨carryIn, hcarryIn⟩ hsourceZero
        (by intro heq; apply hdestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationDistinct; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationSourceRight; exact congrArg Fin.val heq)
        (by intro heq; apply hdestinationScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hsourceLeftScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hsourceRightScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hcarryInScratch; exact congrArg Fin.val heq)
    have htarget := executeInstructions_addCarry_general target
        ⟨freshDestination, hfreshDestinationBound⟩
        ⟨freshCarry, hfreshCarryBound⟩
        ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩
        ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩
        ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩ htargetZero
        (by intro heq; apply hfreshDestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDistinct; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDestinationSourceRight; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshDestinationScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshSourceLeftScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshSourceRightScratch; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryInScratch; exact congrArg Fin.val heq)
    have hsourceCarryResult := congrArg Prod.snd hsource
    have htargetCarryResult := congrArg Prod.snd htarget
    calc
      readRegister (executeInstructions source sourceCode)
          ⟨resultCarry, hresultCarry⟩ =
          (addCarryWords (readRegister source ⟨sourceLeft, hsourceLeft⟩)
            (readRegister source ⟨sourceRight, hsourceRight⟩)
            (readRegister source ⟨carryIn, hcarryIn⟩)).2 := by
              exact hsourceCarryResult
      _ = (addCarryWords (readRegister target
            ⟨wordSsaRead ssa sourceLeft, hsourceLeftSsa⟩)
            (readRegister target ⟨wordSsaRead ssa sourceRight, hsourceRightSsa⟩)
            (readRegister target ⟨wordSsaRead ssa carryIn, hcarryInSsa⟩)).2 := by
              rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
      _ = readRegister (executeInstructions target targetCode)
          ⟨freshCarry, hfreshCarryBound⟩ := by
              exact htargetCarryResult.symm
  · have hsourceMemory :
        (executeInstructions source sourceCode).memory = source.memory := by
      simp [sourceCode, executeInstructions, execute, writeRegister,
        hsourceZero, hdestinationNonzero, hresultCarryNonzero]
    have htargetMemory :
        (executeInstructions target targetCode).memory = target.memory := by
      simp [targetCode, executeInstructions, execute, writeRegister,
        htargetZero, hfreshDestinationNonzero, hfreshCarryNonzero]
    exact hsourceMemory.trans (hmemory.trans htargetMemory.symm)

end Flapjack.RiscV
