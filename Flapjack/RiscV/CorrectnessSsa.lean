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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
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
      readRegister source ⟨riscvRegisterName sourceName, riscvRegisterName_lt_32 hsource⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceName), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rw [wordSsaRenameInst_store]
  simp only [evalWordProg, labRegisterOfNat_of_lt_32 hsource,
    labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 hsourceSsa,
    labRegisterOfNat_of_lt_32 haddressSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.bind_some, Option.map_some, execute]
  rw [haddressValue, hsourceValue]
  simp only [Option.some.injEq]
  apply writeWordValue_memory_congr
  exact hmemory

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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
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
      readRegister source ⟨riscvRegisterName sourceName, riscvRegisterName_lt_32 hsource⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceName), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rcases hoperator with rfl | rfl | rfl | rfl
  · exact evalWordProg_ssaRename_store ssa source target hregister hmemory
      sourceName address hsource haddress hsourceSsa haddressSsa
  · simp [wordSsaRenameInst, evalWordProg, labRegisterOfNat_of_lt_32 hsource,
      labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 hsourceSsa,
      labRegisterOfNat_of_lt_32 haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeByte_memory_congr
    rfl
  · simp [wordSsaRenameInst, evalWordProg, labRegisterOfNat_of_lt_32 hsource,
      labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 hsourceSsa,
      labRegisterOfNat_of_lt_32 haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeWord16_memory_congr
    rfl
  · simp [wordSsaRenameInst, evalWordProg, labRegisterOfNat_of_lt_32 hsource,
      labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 hsourceSsa,
      labRegisterOfNat_of_lt_32 haddressSsa, hsourceValue, haddressValue, hmemory, execute]
    apply writeWord32_memory_congr
    rfl

theorem evalWordProg_ssaRename_load_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWordValue source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWordValue target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWordValue, readByte, hmemory]
  rw [wordSsaRenameInst_load]
  refine ⟨execute source (.loadWord ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadWord ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hdestination,
      labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hfresh,
      labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load8_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load8 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load8 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      BitVec.ofNat width
          (readByte source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩)).toNat =
        BitVec.ofNat width
          (readByte target
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩)).toNat := by
    rw [haddressValue]
    simp [readByte, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.loadByte ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadByte ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hdestination,
      labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hfresh,
      labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load16_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load16 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load16 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWord16 source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWord16 target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord16, readByte, byteAddress, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.loadHalf ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadHalf ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hdestination,
      labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hfresh,
      labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem evalWordProg_ssaRename_load32_destination [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.mem .load32 destination address)) = some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.mem .load32 destination address : WordInst)).2) = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWord32 source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWord32 target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord32, readByte, byteAddress, hmemory]
  rw [wordSsaRenameInst]
  refine ⟨execute source (.load32 ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.load32 ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hdestination,
      labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, labRegisterOfNat_of_lt_32 hfresh,
      labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
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
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.locValue destination label) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa (.locValue destination label)).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  rw [wordSsaRenameProgram_locValue]
  have hzero' : source.registers 0 = target.registers 0 := by
    simpa [readRegister] using hzero
  refine ⟨execute source (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 0
      (BitVec.ofNat width label)),
    execute target (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 0
      (BitVec.ofNat width label)), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, wordLocValueToInstructions, labRegisterOfNat_of_lt_32 hdestination]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, wordLocValueToInstructions, labRegisterOfNat_of_lt_32 hfresh]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination sourceName : Nat)
    (hdestination : destination < 32) (hsource : sourceName < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hsourceSsa : wordSsaRead ssa sourceName < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.assign destination (.var sourceName)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.var sourceName))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister source ⟨riscvRegisterName sourceName, riscvRegisterName_lt_32 hsource⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceName), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister sourceName
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_assign_var]
  refine ⟨execute source (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName sourceName, riscvRegisterName_lt_32 hsource⟩ 0),
    execute target (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa sourceName), riscvRegisterName_lt_32 hsourceSsa⟩ 0), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.map_some, Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.map_some, Option.bind_some, executeInstructions_single]
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
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.assign destination (.const value)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.const value))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  rw [wordSsaRenameProgram_assign_const]
  have hzero' : source.registers 0 = target.registers 0 := by
    simpa [readRegister] using hzero
  refine ⟨execute source (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 0 value),
    execute target (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 0 value),
    ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      labRegisterOfNat_of_lt_32 hdestination]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.map_some, Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      labRegisterOfNat_of_lt_32 hfresh]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.map_some, Option.bind_some, executeInstructions_single]
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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination left right : Nat) (operator : BinOp)
    (hdestination : destination < 32) (hleft : left < 32) (hright : right < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hleftSsa : wordSsaRead ssa left < 32)
    (hrightSsa : wordSsaRead ssa right < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source
          (.assign destination (.op operator [.var left, .var right])) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.var left, .var right]))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hleftValue :
      readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ := by
    have h := hregister left
    simpa [labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hleftSsa, Option.some.injEq] using h
  have hrightValue :
      readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
    have h := hregister right
    simpa [labRegisterOfNat_of_lt_32 hright, labRegisterOfNat_of_lt_32 hrightSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_assign_binary_var_var]
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ + readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
            readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ +
              readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.add ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute target (.add ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
          labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
          labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | sub =>
      have hvalue :
          readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ - readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
            readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ -
              readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.sub ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute target (.sub ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
          labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
          labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | and =>
      have hvalue :
          readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ &&& readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
            readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ &&&
              readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.and ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute target (.and ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
          labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
          labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | or =>
      have hvalue :
          readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ||| readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
            readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ |||
              readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.or ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute target (.or ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
          labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
          labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | xor =>
      have hvalue :
          readRegister source ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ^^^ readRegister source ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
            readRegister target ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ ^^^
              readRegister target ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
        rw [hleftValue, hrightValue]
      refine ⟨execute source (.xor ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute target (.xor ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
          labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
          labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
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
        let register ← labRegisterOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination source : Nat) (operator : BinOp) (value : Word width)
    (hdestination : destination < 32) (hsource : source < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hsourceSsa : wordSsaRead ssa source < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.op operator [.var source, .const value])) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.var source, .const value]))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister source
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_assign_binary_var_const]
  cases operator with
  | add =>
      have hvalue :
          readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ + value =
            readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ + value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ value),
        execute targetState (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | sub =>
      have hvalue :
          readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ - value =
            readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ - value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ (0 - value)),
        execute targetState (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ (0 - value)), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | and =>
      have hvalue :
          readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ &&& value =
            readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ &&& value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.andi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ value),
        execute targetState (.andi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | or =>
      have hvalue :
          readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ ||| value =
            readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ ||| value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.ori ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ value),
        execute targetState (.ori ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | xor =>
      have hvalue :
          readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ ^^^ value =
            readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ ^^^ value := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.xori ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ value),
        execute targetState (.xori ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ value), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
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
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source
          (.assign destination (.op operator [.const left, .const right])) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.assign destination (.op operator [.const left, .const right]))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
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
  refine ⟨execute source (.addi ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 0 result),
    execute target (.addi ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 0 result),
    ?_, ?_, ?_, ?_⟩
  · cases operator <;>
      (simp only [result, evalWordProg, wordExpToInstructions,
        wordExpToInstruction, labRegisterOfNat_of_lt_32 hdestination]
       dsimp only [Bind.bind, Pure.pure]
       simp only [Option.map_some, Option.bind_some, executeInstructions_single])
  · cases operator <;>
      (simp only [result, evalWordProg, wordExpToInstructions,
        wordExpToInstruction, labRegisterOfNat_of_lt_32 hfresh]
       dsimp only [Bind.bind, Pure.pure]
       simp only [Option.map_some, Option.bind_some, executeInstructions_single])
  · simp [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero, hzero']
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_shift_var_const
    (ssa : WordSsaState) (destination : Nat) (operator : Shift)
    (source : Nat) (amount : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift operator (.var source) (.const amount)) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift operator (.var (wordSsaRead ssa source)) (.const amount))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_shift_var_const_destination [NeZero width]
    (ssa : WordSsaState) (sourceState targetState : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination source : Nat) (operator : Shift) (amount : Word width)
    (hdestination : destination < 32) (hsource : source < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hsourceSsa : wordSsaRead ssa source < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hoperator : operator ≠ .ror) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.shift operator (.var source) (.const amount))) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.shift operator (.var source) (.const amount)))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister source
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_assign_shift_var_const]
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩)
              (shiftAmount amount) =
            BitVec.shiftLeft (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩)
              (shiftAmount amount) := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.slli ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ amount),
        execute targetState (.slli ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩
          amount), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩)
              (shiftAmount amount) =
            BitVec.ushiftRight (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩)
              (shiftAmount amount) := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.srli ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ amount),
        execute targetState (.srli ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩
          amount), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩)
              (shiftAmount amount) =
            BitVec.sshiftRight (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩)
              (shiftAmount amount) := by
        rw [hsourceValue]
      refine ⟨execute sourceState (.srai ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ amount),
        execute targetState (.srai ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩
          amount), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | ror => exact (hoperator rfl).elim

theorem wordSsaRenameProgram_assign_shift_var_var
    (ssa : WordSsaState) (destination : Nat) (operator : Shift)
    (left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift operator (.var left) (.var right)) :
          WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift operator (.var (wordSsaRead ssa left))
            (.var (wordSsaRead ssa right)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_shift_var_var_destination [NeZero width]
    (ssa : WordSsaState) (sourceState targetState : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination left right : Nat) (operator : Shift)
    (hdestination : destination < 32) (hleft : left < 32) (hright : right < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hleftSsa : wordSsaRead ssa left < 32)
    (hrightSsa : wordSsaRead ssa right < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hoperator : operator ≠ .ror) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.shift operator (.var left) (.var right))) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.shift operator (.var left) (.var right)))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hleftValue :
      readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ := by
    have h := hregister left
    simpa [labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hleftSsa, Option.some.injEq] using h
  have hrightValue :
      readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
    have h := hregister right
    simpa [labRegisterOfNat_of_lt_32 hright, labRegisterOfNat_of_lt_32 hrightSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_assign_shift_var_var]
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩)
              (shiftAmount (readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩)) =
            BitVec.shiftLeft
              (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩)
              (shiftAmount
                (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩)) := by
        rw [hleftValue, hrightValue]
      refine ⟨execute sourceState (.sll ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute targetState (.sll ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa, labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩)
              (shiftAmount (readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩)) =
            BitVec.ushiftRight
              (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩)
              (shiftAmount
                (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩)) := by
        rw [hleftValue, hrightValue]
      refine ⟨execute sourceState (.srl ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute targetState (.srl ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa, labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩)
              (shiftAmount (readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩)) =
            BitVec.sshiftRight
              (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩)
              (shiftAmount
                (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩)) := by
        rw [hleftValue, hrightValue]
      refine ⟨execute sourceState (.sra ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
          ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩),
        execute targetState (.sra ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
          ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩), ?_, ?_, ?_, ?_⟩
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hright]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simp only [evalWordProg, wordExpToInstructions, wordExpToInstruction,
        labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa, labRegisterOfNat_of_lt_32 hrightSsa]
        dsimp only [Bind.bind, Pure.pure]
        simp only [Option.map_some, Option.bind_some, executeInstructions_single]
      · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
          hfreshNonzero] using hvalue
      · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]
  | ror => exact (hoperator rfl).elim

theorem wordSsaRenameProgram_assign_rotate_var_const
    (ssa : WordSsaState) (destination : Nat) (source : Nat)
    (amount : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift .ror (.var source) (.const amount)) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift .ror (.var (wordSsaRead ssa source)) (.const amount))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_rotate_var_const_destination [NeZero width]
    (ssa : WordSsaState) (sourceState targetState : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination source : Nat) (amount : Word width)
    (hdestination : destination < 32) (hsource : source < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hsourceScratch : source ≠ 31)
    (hsourceSsa : wordSsaRead ssa source < 32)
    (hsourceSsaScratch : wordSsaRead ssa source ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hfreshScratch : (wordSsaFresh ssa destination).2 ≠ 31) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.shift .ror (.var source) (.const amount))) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.shift .ror (.var source) (.const amount)))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hsourceValue :
      readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ := by
    have h := hregister source
    simpa [labRegisterOfNat_of_lt_32 hsource, labRegisterOfNat_of_lt_32 hsourceSsa, Option.some.injEq] using h
  have amount_lt : shiftAmount amount < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  have complement_lt : (width - shiftAmount amount) % width < width :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne width))
  have hsourceFinScratch :
      (⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hsourceScratch
    refine riscvRegisterName_injective_lt_32 hsource (by decide) ?_
    have hval : riscvRegisterName (source) = 31 := congrArg Fin.val heq
    rw [hval, riscvRegisterName_thirtyOne]
  have hsourceSsaFinScratch :
      (⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hsourceSsaScratch
    refine riscvRegisterName_injective_lt_32 hsourceSsa (by decide) ?_
    have hval : riscvRegisterName (wordSsaRead ssa source) = 31 := congrArg Fin.val heq
    rw [hval, riscvRegisterName_thirtyOne]
  have hdestinationFinNonzero :
      (⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  have hdestinationFinScratch :
      (⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hdestinationScratch
    refine riscvRegisterName_injective_lt_32 hdestination (by decide) ?_
    have hval : riscvRegisterName (destination) = 31 := congrArg Fin.val heq
    rw [hval, riscvRegisterName_thirtyOne]
  have hfreshFinNonzero :
      (⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hfreshNonzero
    exact congrArg Fin.val heq
  have hfreshFinScratch :
      (⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hfreshScratch
    refine riscvRegisterName_injective_lt_32 hfresh (by decide) ?_
    have hval : riscvRegisterName ((wordSsaFresh ssa destination).2) = 31 := congrArg Fin.val heq
    rw [hval, riscvRegisterName_thirtyOne]
  rw [wordSsaRenameProgram_assign_rotate_var_const]
  let sourceCode : List (Instruction width) :=
    [.srli 31 ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩ (shiftAmount amount),
     .slli ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩
       (BitVec.ofNat width ((width - shiftAmount amount) % width)),
     .or ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.srli 31 ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩ (shiftAmount amount),
     .slli ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
       ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩
       (BitVec.ofNat width ((width - shiftAmount amount) % width)),
     .or ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
       ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hvalue :
      rotateRight (readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩)
          (shiftAmount amount) =
        rotateRight
          (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩)
          (shiftAmount amount) := by
    rw [hsourceValue]
  have hsourceDestination :
      readRegister (executeInstructions sourceState sourceCode)
          ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        rotateRight (readRegister sourceState ⟨riscvRegisterName source, riscvRegisterName_lt_32 hsource⟩)
          (shiftAmount amount) := by
    simp [sourceCode, executeInstructions, execute, writeRegister, readRegister,
      hsourceFinScratch, hdestinationFinNonzero,
      Ne.symm hdestinationFinScratch]
    rw [shiftAmount_ofNat_of_lt complement_lt,
      shiftAmount_ofNat_of_lt amount_lt]
    simp [rotateRight, shiftAmount, BitVec.or_comm]
  have htargetDestination :
      readRegister (executeInstructions targetState targetCode)
          ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ =
        rotateRight
          (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa source), riscvRegisterName_lt_32 hsourceSsa⟩)
          (shiftAmount amount) := by
    simp [targetCode, executeInstructions, execute, writeRegister, readRegister,
      hsourceSsaFinScratch, hfreshFinNonzero,
      Ne.symm hfreshFinScratch]
    rw [shiftAmount_ofNat_of_lt complement_lt,
      shiftAmount_ofNat_of_lt amount_lt]
    simp [rotateRight, shiftAmount, BitVec.or_comm]
  refine ⟨executeInstructions sourceState sourceCode,
    executeInstructions targetState targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, wordExpToInstructions,
      labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hsource,
      hdestinationScratch, hsourceScratch]
  · simp [targetCode, evalWordProg, wordExpToInstructions,
      labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hsourceSsa,
      hsourceSsaScratch, hfreshScratch]
  · exact (hsourceDestination.trans hvalue).trans htargetDestination.symm
  · simp [sourceCode, targetCode, executeInstructions, execute, writeRegister,
      hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_assign_rotate_var_var
    (ssa : WordSsaState) (destination left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift .ror (.var left) (.var right)) :
          WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift .ror (.var (wordSsaRead ssa left))
            (.var (wordSsaRead ssa right)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_assign_rotate_var_var_destination [NeZero width]
    (ssa : WordSsaState) (sourceState targetState : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister sourceState register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister targetState register)))
    (hmemory : sourceState.memory = targetState.memory)
    (destination left right : Nat)
    (hdestination : destination < 32) (hleft : left < 32) (hright : right < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31)
    (hleftSsa : wordSsaRead ssa left < 32)
    (hrightSsa : wordSsaRead ssa right < 32)
    (hdestinationSsaScratch :
      (wordSsaFresh ssa destination).2 ≠ 31)
    (hleftSsaScratch : wordSsaRead ssa left ≠ 31)
    (hrightSsaScratch : wordSsaRead ssa right ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hzeroSource : readRegister sourceState 0 = 0)
    (hzeroTarget : readRegister targetState 0 = 0)
    (hwidth : width = 32 ∨ width = 64) :
    ∃ source' target',
      evalWordProg sourceState
          (.assign destination (.shift .ror (.var left) (.var right))) = some source' ∧
      evalWordProg targetState
          (wordSsaRenameProgram ssa
            (.assign destination (.shift .ror (.var left) (.var right)))).2 =
        some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hleftValue :
      readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ := by
    have h := hregister left
    simpa [labRegisterOfNat_of_lt_32 hleft, labRegisterOfNat_of_lt_32 hleftSsa, Option.some.injEq] using h
  have hrightValue :
      readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ =
        readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ := by
    have h := hregister right
    simpa [labRegisterOfNat_of_lt_32 hright, labRegisterOfNat_of_lt_32 hrightSsa, Option.some.injEq] using h
  have hleftFinScratch :
      (⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ : Fin 32) ≠ 31 := by
    exact riscvRegisterName_fin_ne_thirtyOne hleft hleftScratch
  have hrightFinScratch :
      (⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩ : Fin 32) ≠ 31 := by
    exact riscvRegisterName_fin_ne_thirtyOne hright hrightScratch
  have hleftSsaFinScratch :
      (⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ : Fin 32) ≠ 31 := by
    exact riscvRegisterName_fin_ne_thirtyOne hleftSsa hleftSsaScratch
  have hrightSsaFinScratch :
      (⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩ : Fin 32) ≠ 31 := by
    exact riscvRegisterName_fin_ne_thirtyOne hrightSsa hrightSsaScratch
  have hdestinationFinNonzero :
      (⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hdestinationNonzero
    exact congrArg Fin.val heq
  have hdestinationFinScratch :
      (⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ : Fin 32) ≠ 31 := by
    intro heq
    apply hdestinationScratch
    refine riscvRegisterName_injective_lt_32 hdestination (by decide) ?_
    have hval : riscvRegisterName (destination) = 31 := congrArg Fin.val heq
    rw [hval, riscvRegisterName_thirtyOne]
  have hfreshFinNonzero :
      (⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ : Fin 32) ≠ 0 := by
    intro heq
    apply hfreshNonzero
    exact congrArg Fin.val heq
  have hfreshFinScratch :
      (⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ : Fin 32) ≠ 31 := by
    exact riscvRegisterName_fin_ne_thirtyOne hfresh hdestinationSsaScratch
  have hshift (value : Word width) :
      shiftAmount (BitVec.ofNat width width - value) =
        (width - shiftAmount value) % width := by
    rcases hwidth with rfl | rfl <;>
      simp [shiftAmount, BitVec.toNat_sub] <;> omega
  have hzeroSource' : sourceState.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : targetState.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  have hvalue :
      rotateRight
          (readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩)
          (shiftAmount (readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩)) =
        rotateRight
          (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩)
          (shiftAmount
            (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩)) := by
    rw [hleftValue, hrightValue]
  rw [wordSsaRenameProgram_assign_rotate_var_var]
  let sourceCode : List (Instruction width) :=
    [.ori 31 0 (BitVec.ofNat width width),
     .sub 31 31 ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩,
     .sll 31 ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ 31,
     .srl ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩ ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩,
     .or ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.ori 31 0 (BitVec.ofNat width width),
     .sub 31 31 ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩,
     .sll 31 ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩ 31,
     .srl ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
       ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩
       ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩,
     .or ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
       ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hsourceDestination :
      readRegister (executeInstructions sourceState sourceCode)
          ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        rotateRight
          (readRegister sourceState ⟨riscvRegisterName left, riscvRegisterName_lt_32 hleft⟩)
          (shiftAmount (readRegister sourceState ⟨riscvRegisterName right, riscvRegisterName_lt_32 hright⟩)) := by
    simp [sourceCode, executeInstructions, execute, readRegister, writeRegister,
      hzeroSource', hleftFinScratch, hrightFinScratch,
      hdestinationFinNonzero, Ne.symm hdestinationFinScratch]
    rw [hshift]
    simp [rotateRight, shiftAmount]
  have htargetDestination :
      readRegister (executeInstructions targetState targetCode)
          ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ =
        rotateRight
          (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa left), riscvRegisterName_lt_32 hleftSsa⟩)
          (shiftAmount
            (readRegister targetState ⟨riscvRegisterName (wordSsaRead ssa right), riscvRegisterName_lt_32 hrightSsa⟩)) := by
    simp [targetCode, executeInstructions, execute, readRegister, writeRegister,
      hzeroTarget', hleftSsaFinScratch, hrightSsaFinScratch,
      hfreshFinNonzero, Ne.symm hfreshFinScratch]
    rw [hshift]
    simp [rotateRight, shiftAmount]
  refine ⟨executeInstructions sourceState sourceCode,
    executeInstructions targetState targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, wordExpToInstructions,
      labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hleft,
      labRegisterOfNat_of_lt_32 hright, hdestinationScratch, hleftScratch,
      hrightScratch]
  · simp [targetCode, evalWordProg, wordExpToInstructions,
      labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hleftSsa,
      labRegisterOfNat_of_lt_32 hrightSsa, hdestinationSsaScratch,
      hleftSsaScratch, hrightSsaScratch]
  · exact (hsourceDestination.trans hvalue).trans htargetDestination.symm
  · simp [sourceCode, targetCode, executeInstructions, execute, writeRegister,
      hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_store_var
    (ssa : WordSsaState) (address value : Nat) :
    wordSsaRenameProgram ssa
        (.store (.var address) value : WordProg α) =
      (ssa, .store (.var (wordSsaRead ssa address))
        (wordSsaRead ssa value)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_store_var [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (address value : Nat)
    (haddress : address < 32) (hvalue : value < 32)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hvalueSsa : wordSsaRead ssa value < 32) :
    (evalWordProg source (.store (.var address) value)).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa (.store (.var address) value)).2).map
        (fun state => state.memory) := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_store_var]
  simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions, wordInstToInstruction,
    labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 hvalue,
    labRegisterOfNat_of_lt_32 haddressSsa, labRegisterOfNat_of_lt_32 hvalueSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.map_some, Option.bind_some, executeInstructions_single, execute, Option.some.injEq]
  rw [haddressValue, hvalueValue]
  apply writeWordValue_memory_congr
  exact hmemory

theorem wordSsaRenameProgram_shareInst_load_var
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.shareInst .load destination (.var address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load destination (.var address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWordValue source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWordValue target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWordValue, readByte, hmemory]
  rw [wordSsaRenameProgram_shareInst_load_var]
  refine ⟨execute source (.loadWord ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadWord ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_load8_var
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load8 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load8 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load8 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.shareInst .load8 destination (.var address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load8 destination (.var address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      BitVec.ofNat width
          (readByte source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩)).toNat =
        BitVec.ofNat width
          (readByte target
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩)).toNat := by
    rw [haddressValue]
    simp [readByte, hmemory]
  rw [wordSsaRenameProgram_shareInst_load8_var]
  refine ⟨execute source (.loadByte ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadByte ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_load16_var
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load16 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load16 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load16 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.shareInst .load16 destination (.var address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load16 destination (.var address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWord16 source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWord16 target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord16, readByte, byteAddress, hmemory]
  rw [wordSsaRenameProgram_shareInst_load16_var]
  refine ⟨execute source (.loadHalf ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.loadHalf ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_load32_var
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load32 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load32 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load32 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination address : Nat)
    (hdestination : destination < 32) (haddress : address < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (haddressSsa : wordSsaRead ssa address < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.shareInst .load32 destination (.var address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load32 destination (.var address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  have hloadValue :
      readWord32 source (readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩) =
        readWord32 target
          (readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩) := by
    rw [haddressValue]
    simp [readWord32, readByte, byteAddress, hmemory]
  rw [wordSsaRenameProgram_shareInst_load32_var]
  refine ⟨execute source (.load32 ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩),
    execute target (.load32 ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 haddress]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions,
      wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 haddressSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Option.bind_some, executeInstructions_single]
  · simpa [execute, writeRegister, readRegister, hdestinationNonzero,
      hfreshNonzero] using hloadValue
  · simp [execute, writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_store_var
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store value (.var address) : WordProg α) =
      (ssa, .shareInst .store (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (value address : Nat)
    (hvalue : value < 32) (haddress : address < 32)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.shareInst .store value (.var address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store value (.var address))).2).map
        (fun state => state.memory) := by
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_shareInst_store_var]
  simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions, wordInstToInstruction,
    labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 haddress,
    labRegisterOfNat_of_lt_32 hvalueSsa, labRegisterOfNat_of_lt_32 haddressSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.map_some, Option.bind_some, executeInstructions_single, execute, Option.some.injEq]
  rw [haddressValue, hvalueValue]
  apply writeWordValue_memory_congr
  exact hmemory

theorem wordSsaRenameProgram_shareInst_store8_var
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store8 value (.var address) : WordProg α) =
      (ssa, .shareInst .store8 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store8 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (value address : Nat)
    (hvalue : value < 32) (haddress : address < 32)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.shareInst .store8 value (.var address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store8 value (.var address))).2).map
        (fun state => state.memory) := by
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_shareInst_store8_var]
  simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions, wordInstToInstruction,
    labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 haddress,
    labRegisterOfNat_of_lt_32 hvalueSsa, labRegisterOfNat_of_lt_32 haddressSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.map_some, Option.bind_some, executeInstructions_single, execute, Option.some.injEq]
  rw [haddressValue, hvalueValue]
  apply writeByte_memory_congr
  exact hmemory

theorem wordSsaRenameProgram_shareInst_store16_var
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store16 value (.var address) : WordProg α) =
      (ssa, .shareInst .store16 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store16 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (value address : Nat)
    (hvalue : value < 32) (haddress : address < 32)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.shareInst .store16 value (.var address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store16 value (.var address))).2).map
        (fun state => state.memory) := by
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_shareInst_store16_var]
  simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions, wordInstToInstruction,
    labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 haddress,
    labRegisterOfNat_of_lt_32 hvalueSsa, labRegisterOfNat_of_lt_32 haddressSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.map_some, Option.bind_some, executeInstructions_single, execute, Option.some.injEq]
  rw [haddressValue, hvalueValue]
  apply writeWord16_memory_congr
  exact hmemory

theorem wordSsaRenameProgram_shareInst_store32_var
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store32 value (.var address) : WordProg α) =
      (ssa, .shareInst .store32 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store32 [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (value address : Nat)
    (hvalue : value < 32) (haddress : address < 32)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (haddressSsa : wordSsaRead ssa address < 32) :
    (evalWordProg source (.shareInst .store32 value (.var address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store32 value (.var address))).2).map
        (fun state => state.memory) := by
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have haddressValue :
      readRegister source ⟨riscvRegisterName address, riscvRegisterName_lt_32 haddress⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa address), riscvRegisterName_lt_32 haddressSsa⟩ := by
    have h := hregister address
    simpa [labRegisterOfNat_of_lt_32 haddress, labRegisterOfNat_of_lt_32 haddressSsa, Option.some.injEq] using h
  rw [wordSsaRenameProgram_shareInst_store32_var]
  simp only [evalWordProg, evalWordShareInst, wordShareInstToInstructions, wordInstToInstruction,
    labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 haddress,
    labRegisterOfNat_of_lt_32 hvalueSsa, labRegisterOfNat_of_lt_32 haddressSsa]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Option.map_some, Option.bind_some, executeInstructions_single, execute, Option.some.injEq]
  rw [haddressValue, hvalueValue]
  apply writeWord32_memory_congr
  exact hmemory

theorem wordSsaRenameProgram_shareInst_load_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (destination : Nat) (address : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hfreshScratch : (wordSsaFresh ssa destination).2 ≠ 31) :
    ∃ source' target',
      evalWordProg source (.shareInst .load destination (.const address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load destination (.const address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  rw [wordSsaRenameProgram_shareInst_load_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .loadWord ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .loadWord ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .load destination (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hfresh,
      hdestination, hdestinationScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .load
        (wordSsaFresh ssa destination).2 (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh,
      hfresh, hfreshScratch]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, evalWordShareInst,
      hsourceCompile, executeInstructions]
  · simp [targetCode, evalWordProg, evalWordShareInst,
      htargetCompile, executeInstructions]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, readRegister, hdestinationNonzero, hfreshNonzero,
      hzeroSource', hzeroTarget']
    simp [readWordValue, readByte, hmemory]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_store_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (value : Nat) (address : Word width)
    (hvalue : value < 32)
    (hvalueScratch : value ≠ 31)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (hvalueSsaScratch : wordSsaRead ssa value ≠ 31) :
    (evalWordProg source (.shareInst .store value (.const address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store value (.const address))).2).map
        (fun state => state.memory) := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have hvalueValue' :
      source.registers ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        target.registers ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    simpa [readRegister] using hvalueValue
  have hvalueScratch' : (⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalue hvalueScratch
  have hvalueSsaScratch' :
      (⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalueSsa hvalueSsaScratch
  rw [wordSsaRenameProgram_shareInst_store_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .storeWord ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .storeWord ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .store value (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalue,
      hvalue, hvalueScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .store
        (wordSsaRead ssa value) (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalueSsa,
      hvalueSsa, hvalueSsaScratch]
  simp [evalWordProg, evalWordShareInst, hsourceCompile, htargetCompile,
    sourceCode, targetCode, executeInstructions, execute, writeRegister,
    readRegister, hvalueValue', hzeroSource', hzeroTarget',
    hvalueScratch', hvalueSsaScratch', hmemory]
  apply writeWordValue_memory_congr
  rfl

theorem wordSsaRenameProgram_shareInst_load8_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load8 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load8 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load8_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (destination : Nat) (address : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hfreshScratch : (wordSsaFresh ssa destination).2 ≠ 31) :
    ∃ source' target',
      evalWordProg source (.shareInst .load8 destination (.const address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load8 destination (.const address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  rw [wordSsaRenameProgram_shareInst_load8_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .loadByte ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .loadByte ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .load8 destination (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hfresh,
      hdestination, hdestinationScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .load8
        (wordSsaFresh ssa destination).2 (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh,
      hfresh, hfreshScratch]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, evalWordShareInst,
      hsourceCompile, executeInstructions]
  · simp [targetCode, evalWordProg, evalWordShareInst,
      htargetCompile, executeInstructions]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, readRegister, hdestinationNonzero, hfreshNonzero,
      hzeroSource', hzeroTarget']
    simp [readByte, hmemory]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_load16_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load16 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load16 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load16_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (destination : Nat) (address : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hfreshScratch : (wordSsaFresh ssa destination).2 ≠ 31) :
    ∃ source' target',
      evalWordProg source (.shareInst .load16 destination (.const address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load16 destination (.const address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  rw [wordSsaRenameProgram_shareInst_load16_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .loadHalf ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .loadHalf ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .load16 destination (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hfresh,
      hdestination, hdestinationScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .load16
        (wordSsaFresh ssa destination).2 (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh,
      hfresh, hfreshScratch]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, evalWordShareInst,
      hsourceCompile, executeInstructions]
  · simp [targetCode, evalWordProg, evalWordShareInst,
      htargetCompile, executeInstructions]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, readRegister, hdestinationNonzero, hfreshNonzero,
      hzeroSource', hzeroTarget']
    simp [readWord16, readByte, hmemory]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_load32_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load32 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load32 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_load32_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (destination : Nat) (address : Word width)
    (hdestination : destination < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdestinationScratch : destination ≠ 31)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0)
    (hfreshScratch : (wordSsaFresh ssa destination).2 ≠ 31) :
    ∃ source' target',
      evalWordProg source (.shareInst .load32 destination (.const address)) = some source' ∧
      evalWordProg target
          (wordSsaRenameProgram ssa
            (.shareInst .load32 destination (.const address))).2 = some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  rw [wordSsaRenameProgram_shareInst_load32_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .load32 ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .load32 ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .load32 destination (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hfresh,
      hdestination, hdestinationScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .load32
        (wordSsaFresh ssa destination).2 (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hfresh,
      hfresh, hfreshScratch]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, evalWordShareInst,
      hsourceCompile, executeInstructions]
  · simp [targetCode, evalWordProg, evalWordShareInst,
      htargetCompile, executeInstructions]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, readRegister, hdestinationNonzero, hfreshNonzero,
      hzeroSource', hzeroTarget']
    simp [readWord32, readByte, byteAddress, hmemory]
  · simp [sourceCode, targetCode, executeInstructions, execute,
      writeRegister, hmemory, hdestinationNonzero, hfreshNonzero]

theorem wordSsaRenameProgram_shareInst_store8_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store8 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store8 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store8_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (value : Nat) (address : Word width)
    (hvalue : value < 32)
    (hvalueScratch : value ≠ 31)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (hvalueSsaScratch : wordSsaRead ssa value ≠ 31) :
    (evalWordProg source (.shareInst .store8 value (.const address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store8 value (.const address))).2).map
        (fun state => state.memory) := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have hvalueValue' :
      source.registers ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        target.registers ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    simpa [readRegister] using hvalueValue
  have hvalueScratch' : (⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalue hvalueScratch
  have hvalueSsaScratch' :
      (⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalueSsa hvalueSsaScratch
  rw [wordSsaRenameProgram_shareInst_store8_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .storeByte ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .storeByte ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .store8 value (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalue,
      hvalue, hvalueScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .store8
        (wordSsaRead ssa value) (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalueSsa,
      hvalueSsa, hvalueSsaScratch]
  simp [evalWordProg, evalWordShareInst, hsourceCompile, htargetCompile,
    sourceCode, targetCode, executeInstructions, execute, writeRegister,
    readRegister, hvalueValue', hzeroSource', hzeroTarget',
    hvalueScratch', hvalueSsaScratch', hmemory]
  apply writeByte_memory_congr
  rfl

theorem wordSsaRenameProgram_shareInst_store16_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store16 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store16 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store16_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (value : Nat) (address : Word width)
    (hvalue : value < 32)
    (hvalueScratch : value ≠ 31)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (hvalueSsaScratch : wordSsaRead ssa value ≠ 31) :
    (evalWordProg source (.shareInst .store16 value (.const address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store16 value (.const address))).2).map
        (fun state => state.memory) := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have hvalueValue' :
      source.registers ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        target.registers ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    simpa [readRegister] using hvalueValue
  have hvalueScratch' : (⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalue hvalueScratch
  have hvalueSsaScratch' :
      (⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalueSsa hvalueSsaScratch
  rw [wordSsaRenameProgram_shareInst_store16_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .storeHalf ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .storeHalf ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .store16 value (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalue,
      hvalue, hvalueScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .store16
        (wordSsaRead ssa value) (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalueSsa,
      hvalueSsa, hvalueSsaScratch]
  simp [evalWordProg, evalWordShareInst, hsourceCompile, htargetCompile,
    sourceCode, targetCode, executeInstructions, execute, writeRegister,
    readRegister, hvalueValue', hzeroSource', hzeroTarget',
    hvalueScratch', hvalueSsaScratch', hmemory]
  apply writeWord16_memory_congr
  rfl

theorem wordSsaRenameProgram_shareInst_store32_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store32 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store32 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem evalWordProg_ssaRename_program_share_store32_const [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hzeroSource : readRegister source 0 = 0)
    (hzeroTarget : readRegister target 0 = 0)
    (value : Nat) (address : Word width)
    (hvalue : value < 32)
    (hvalueScratch : value ≠ 31)
    (hvalueSsa : wordSsaRead ssa value < 32)
    (hvalueSsaScratch : wordSsaRead ssa value ≠ 31) :
    (evalWordProg source (.shareInst .store32 value (.const address))).map
        (fun state => state.memory) =
      (evalWordProg target
        (wordSsaRenameProgram ssa
          (.shareInst .store32 value (.const address))).2).map
        (fun state => state.memory) := by
  have hzeroSource' : source.registers 0 = 0 := by
    simpa [readRegister] using hzeroSource
  have hzeroTarget' : target.registers 0 = 0 := by
    simpa [readRegister] using hzeroTarget
  have hvalueValue :
      readRegister source ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    have h := hregister value
    simpa [labRegisterOfNat_of_lt_32 hvalue, labRegisterOfNat_of_lt_32 hvalueSsa, Option.some.injEq] using h
  have hvalueValue' :
      source.registers ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ =
        target.registers ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ := by
    simpa [readRegister] using hvalueValue
  have hvalueScratch' : (⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalue hvalueScratch
  have hvalueSsaScratch' :
      (⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ : Fin 32) ≠ 31 :=
    riscvRegisterName_fin_ne_thirtyOne hvalueSsa hvalueSsaScratch
  rw [wordSsaRenameProgram_shareInst_store32_const]
  let sourceCode : List (Instruction width) :=
    [.addi 31 0 address, .store32 ⟨riscvRegisterName value, riscvRegisterName_lt_32 hvalue⟩ 31]
  let targetCode : List (Instruction width) :=
    [.addi 31 0 address,
     .store32 ⟨riscvRegisterName (wordSsaRead ssa value), riscvRegisterName_lt_32 hvalueSsa⟩ 31]
  have hsourceCompile :
      wordShareInstToInstructions (width := width) .store32 value (.const address) =
        some sourceCode := by
    simp [sourceCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalue,
      hvalue, hvalueScratch]
  have htargetCompile :
      wordShareInstToInstructions (width := width) .store32
        (wordSsaRead ssa value) (.const address) =
        some targetCode := by
    simp [targetCode, wordShareInstToInstructions, wordExpToInstructions,
      wordExpToInstruction, wordInstToInstruction, labRegisterOfNat_of_lt_32 hvalueSsa,
      hvalueSsa, hvalueSsaScratch]
  simp [evalWordProg, evalWordShareInst, hsourceCompile, htargetCompile,
    sourceCode, targetCode, executeInstructions, execute, writeRegister,
    readRegister, hvalueValue', hzeroSource', hzeroTarget',
    hvalueScratch', hvalueSsaScratch', hmemory]
  apply writeWord32_memory_congr
  rfl

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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (destination dividend divisor : Nat)
    (hdestination : destination < 32) (hdividend : dividend < 32)
    (hdivisor : divisor < 32)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hdividendSsa : wordSsaRead ssa dividend < 32)
    (hdivisorSsa : wordSsaRead ssa divisor < 32)
    (hfresh : (wordSsaFresh ssa destination).2 < 32)
    (hfreshNonzero : riscvRegisterName ((wordSsaFresh ssa destination).2) ≠ 0) :
    ∃ source' target',
      evalWordProg source (.inst (.arith (.div destination dividend divisor))) =
          some source' ∧
      evalWordProg target
          (.inst (wordSsaRenameInst ssa
            (.arith (.div destination dividend divisor) : WordInst)).2) =
          some target' ∧
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩ ∧
      source'.memory = target'.memory := by
  have hdividendValue :
      readRegister source ⟨riscvRegisterName dividend, riscvRegisterName_lt_32 hdividend⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa dividend), riscvRegisterName_lt_32 hdividendSsa⟩ := by
    have h := hregister dividend
    simpa [labRegisterOfNat_of_lt_32 hdividend, labRegisterOfNat_of_lt_32 hdividendSsa, Option.some.injEq] using h
  have hdivisorValue :
      readRegister source ⟨riscvRegisterName divisor, riscvRegisterName_lt_32 hdivisor⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa divisor), riscvRegisterName_lt_32 hdivisorSsa⟩ := by
    have h := hregister divisor
    simpa [labRegisterOfNat_of_lt_32 hdivisor, labRegisterOfNat_of_lt_32 hdivisorSsa, Option.some.injEq] using h
  rw [wordSsaRenameInst_div]
  refine ⟨execute source (.divU ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
      ⟨riscvRegisterName dividend, riscvRegisterName_lt_32 hdividend⟩ ⟨riscvRegisterName divisor, riscvRegisterName_lt_32 hdivisor⟩),
    execute target (.divU ⟨riscvRegisterName ((wordSsaFresh ssa destination).2), riscvRegisterName_lt_32 hfresh⟩
      ⟨riscvRegisterName (wordSsaRead ssa dividend), riscvRegisterName_lt_32 hdividendSsa⟩
      ⟨riscvRegisterName (wordSsaRead ssa divisor), riscvRegisterName_lt_32 hdivisorSsa⟩), ?_, ?_, ?_, ?_⟩
  · simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
      labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hdividend, labRegisterOfNat_of_lt_32 hdivisor, executeInstructions]
  · simp [evalWordProg, wordArithToInstructions, wordArithToInstruction,
      labRegisterOfNat_of_lt_32 hfresh, labRegisterOfNat_of_lt_32 hdividendSsa, labRegisterOfNat_of_lt_32 hdivisorSsa, executeInstructions]
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
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hdestinationLeft : destinationLeft < 32)
    (hdestinationRight : destinationRight < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hdestinationLeftNonzero : riscvRegisterName destinationLeft ≠ 0)
    (hdestinationRightNonzero : riscvRegisterName destinationRight ≠ 0)
    (hdestinationDistinct : destinationLeft ≠ destinationRight)
    (hdestinationLeftSourceLeft : destinationLeft ≠ sourceLeft)
    (hdestinationLeftSourceRight : destinationLeft ≠ sourceRight)
    (hsourceLeftSsa : wordSsaRead ssa sourceLeft < 32)
    (hsourceRightSsa : wordSsaRead ssa sourceRight < 32)
    (hfreshLeftBound : freshLeft < 32) (hfreshRightBound : freshRight < 32)
    (hfreshLeftNonzero : riscvRegisterName freshLeft ≠ 0) (hfreshRightNonzero : riscvRegisterName freshRight ≠ 0)
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
      readRegister source' ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ =
        readRegister target' ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ ∧
      readRegister source' ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ =
        readRegister target' ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ ∧
      source'.memory = target'.memory := by
  have hsourceLeftValue :
      readRegister source ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ := by
    have h := hregister sourceLeft
    simpa [labRegisterOfNat_of_lt_32 hsourceLeft, labRegisterOfNat_of_lt_32 hsourceLeftSsa, Option.some.injEq] using h
  have hsourceRightValue :
      readRegister source ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩ := by
    have h := hregister sourceRight
    simpa [labRegisterOfNat_of_lt_32 hsourceRight, labRegisterOfNat_of_lt_32 hsourceRightSsa, Option.some.injEq] using h
  rw [wordSsaRenameInst]
  simp only [hfirst, hsecond]
  have hdestinationLeftNonzero' :
      (⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ : Fin 32) ≠ 0 :=
    fun h => hdestinationLeftNonzero (congrArg Fin.val h)
  have hdestinationRightNonzero' :
      (⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ : Fin 32) ≠ 0 :=
    fun h => hdestinationRightNonzero (congrArg Fin.val h)
  have hfreshLeftNonzero' :
      (⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ : Fin 32) ≠ 0 :=
    fun h => hfreshLeftNonzero (congrArg Fin.val h)
  have hfreshRightNonzero' :
      (⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ : Fin 32) ≠ 0 :=
    fun h => hfreshRightNonzero (congrArg Fin.val h)
  have hdestinationDistinct' :
      (⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ : Fin 32) ≠
        ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ :=
    riscvRegisterName_fin_ne hdestinationLeft hdestinationRight hdestinationDistinct
  have hfreshDistinct' :
      (⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ : Fin 32) ≠
        ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ :=
    riscvRegisterName_fin_ne hfreshLeftBound hfreshRightBound hfreshDistinct
  have hdestinationLeftSourceLeft' :
      (⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ : Fin 32) ≠
        ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ :=
    riscvRegisterName_fin_ne hdestinationLeft hsourceLeft hdestinationLeftSourceLeft
  have hdestinationLeftSourceRight' :
      (⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ : Fin 32) ≠
        ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩ :=
    riscvRegisterName_fin_ne hdestinationLeft hsourceRight hdestinationLeftSourceRight
  have hfreshLeftSourceLeft' :
      (⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ : Fin 32) ≠
        ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ :=
    riscvRegisterName_fin_ne hfreshLeftBound hsourceLeftSsa hfreshLeftSourceLeft
  have hfreshLeftSourceRight' :
      (⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ : Fin 32) ≠
        ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩ :=
    riscvRegisterName_fin_ne hfreshLeftBound hsourceRightSsa hfreshLeftSourceRight
  refine ⟨executeInstructions source
      [.mulHU ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩
          ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
       .mul ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩
          ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩],
    executeInstructions target
      [.mulHU ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩
          ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
       .mul ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩
          ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
          ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalWordProg, wordArithToInstructions,
      labRegisterOfNat_of_lt_32 hdestinationLeft, labRegisterOfNat_of_lt_32 hdestinationRight,
      labRegisterOfNat_of_lt_32 hsourceLeft, labRegisterOfNat_of_lt_32 hsourceRight]
    dsimp only [Bind.bind, Pure.pure]
    simp [Option.map_some, Option.bind_some, executeInstructions_single,
      hdestinationLeftSourceLeft, hdestinationLeftSourceRight]
  · simp only [evalWordProg, wordArithToInstructions,
      labRegisterOfNat_of_lt_32 hfreshLeftBound, labRegisterOfNat_of_lt_32 hfreshRightBound,
      labRegisterOfNat_of_lt_32 hsourceLeftSsa, labRegisterOfNat_of_lt_32 hsourceRightSsa]
    dsimp only [Bind.bind, Pure.pure]
    simp [Option.map_some, Option.bind_some, executeInstructions_single,
      hfreshLeftSourceLeft, hfreshLeftSourceRight]
  · have hresult := executeInstructions_longMul_general source
        ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩
        hdestinationLeftNonzero' hdestinationRightNonzero'
        hdestinationDistinct' hdestinationLeftSourceLeft'
        hdestinationLeftSourceRight'
    have hleft := congrArg Prod.fst hresult
    have htarget := executeInstructions_longMul_general target
        ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩
        hfreshLeftNonzero' hfreshRightNonzero' hfreshDistinct'
        hfreshLeftSourceLeft' hfreshLeftSourceRight'
    have htargetLeft := congrArg Prod.fst htarget
    calc
      readRegister (executeInstructions source
        [.mulHU ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩
            ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
         .mul ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩
            ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩])
          ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ = _ := hleft
      _ = BitVec.ofNat width
          ((readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩).toNat *
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩).toNat /
            2 ^ width) := by rw [hsourceLeftValue, hsourceRightValue]
      _ = readRegister (executeInstructions target
        [.mulHU ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
         .mul ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩])
          ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ := htargetLeft.symm
  · have hresult := executeInstructions_longMul_general source
        ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩ ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩
        hdestinationLeftNonzero' hdestinationRightNonzero'
        hdestinationDistinct' hdestinationLeftSourceLeft'
        hdestinationLeftSourceRight'
    have hright := congrArg Prod.snd hresult
    have htarget := executeInstructions_longMul_general target
        ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩ ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩
        hfreshLeftNonzero' hfreshRightNonzero' hfreshDistinct'
        hfreshLeftSourceLeft' hfreshLeftSourceRight'
    have htargetRight := congrArg Prod.snd htarget
    calc
      readRegister (executeInstructions source
        [.mulHU ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩
            ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
         .mul ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩
            ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩])
          ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩ = _ := hright
      _ = readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ *
          readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩ := by
            rw [hsourceLeftValue, hsourceRightValue]
      _ = readRegister (executeInstructions target
        [.mulHU ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
         .mul ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
            ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩])
          ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩ := htargetRight.symm
  · have hsourceMemory :
        (executeInstructions source
          [.mulHU ⟨riscvRegisterName destinationLeft, riscvRegisterName_lt_32 hdestinationLeft⟩
              ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
           .mul ⟨riscvRegisterName destinationRight, riscvRegisterName_lt_32 hdestinationRight⟩
              ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩]).memory =
          source.memory := by
      simp [executeInstructions, execute, writeRegister,
        hdestinationLeftNonzero', hdestinationRightNonzero']
    have htargetMemory :
        (executeInstructions target
          [.mulHU ⟨riscvRegisterName freshLeft, riscvRegisterName_lt_32 hfreshLeftBound⟩
              ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
              ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
           .mul ⟨riscvRegisterName freshRight, riscvRegisterName_lt_32 hfreshRightBound⟩
              ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
              ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩]).memory =
          target.memory := by
      simp [executeInstructions, execute, writeRegister,
        hfreshLeftNonzero', hfreshRightNonzero']
    exact hsourceMemory.trans (hmemory.trans htargetMemory.symm)

theorem evalWordProg_ssaRename_addCarry_destinations [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (first second : WordSsaState) (freshDestination freshCarry : Nat)
    (destination resultCarry sourceLeft sourceRight carryIn : Nat)
    (hfirst : wordSsaFresh ssa destination = (first, freshDestination))
    (hsecond : wordSsaFresh first resultCarry = (second, freshCarry))
    (hregister : ∀ name,
      (do
        let register ← labRegisterOfNat name
        pure (readRegister source register)) =
      (do
        let register ← labRegisterOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (hdestination : destination < 32) (hresultCarry : resultCarry < 32)
    (hsourceLeft : sourceLeft < 32) (hsourceRight : sourceRight < 32)
    (hcarryIn : carryIn < 32)
    (hsourceZero : readRegister source 0 = 0)
    (htargetZero : readRegister target 0 = 0)
    (hdestinationNonzero : riscvRegisterName destination ≠ 0)
    (hresultCarryNonzero : riscvRegisterName resultCarry ≠ 0)
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
    (hfreshDestinationNonzero : riscvRegisterName freshDestination ≠ 0)
    (hfreshCarryNonzero : riscvRegisterName freshCarry ≠ 0)
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
      readRegister source' ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
        readRegister target' ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩ ∧
      readRegister source' ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩ =
        readRegister target' ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩ ∧
      source'.memory = target'.memory := by
  have hsourceLeftValue :
      readRegister source ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩ := by
    have h := hregister sourceLeft
    simpa [labRegisterOfNat_of_lt_32 hsourceLeft, labRegisterOfNat_of_lt_32 hsourceLeftSsa, Option.some.injEq] using h
  have hsourceRightValue :
      readRegister source ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩ := by
    have h := hregister sourceRight
    simpa [labRegisterOfNat_of_lt_32 hsourceRight, labRegisterOfNat_of_lt_32 hsourceRightSsa, Option.some.injEq] using h
  have hcarryInValue :
      readRegister source ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩ =
        readRegister target ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩ := by
    have h := hregister carryIn
    simpa [labRegisterOfNat_of_lt_32 hcarryIn, labRegisterOfNat_of_lt_32 hcarryInSsa, Option.some.injEq] using h
  rw [wordSsaRenameInst]
  simp only [hfirst, hsecond]
  let sourceCode : List (Instruction width) :=
    [.sltu 31 0 ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩,
     .add ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
       ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
     .sltu ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩
       ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩,
     .add ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩
       ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31,
     .sltu 31 ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ 31,
     .or ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩
       ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩ 31]
  let targetCode : List (Instruction width) :=
    [.sltu 31 0 ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩,
     .add ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩
       ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
       ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
     .sltu ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩
       ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩
       ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩,
     .add ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩
       ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩ 31,
     .sltu 31 ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩ 31,
     .or ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩
       ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩ 31]
  refine ⟨executeInstructions source sourceCode,
    executeInstructions target targetCode, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sourceCode, evalWordProg, wordArithToInstructions,
      labRegisterOfNat_of_lt_32 hdestination, labRegisterOfNat_of_lt_32 hresultCarry,
      labRegisterOfNat_of_lt_32 hsourceLeft, labRegisterOfNat_of_lt_32 hsourceRight,
      labRegisterOfNat_of_lt_32 hcarryIn, hdestination, hresultCarry, hsourceLeft, hsourceRight,
      hcarryIn, hdestinationScratch, hresultCarryScratch,
      hsourceLeftScratch, hsourceRightScratch, hcarryInScratch,
      executeInstructions]
  · simp [targetCode, evalWordProg, wordArithToInstructions,
      labRegisterOfNat_of_lt_32 hfreshDestinationBound, labRegisterOfNat_of_lt_32 hfreshCarryBound,
      labRegisterOfNat_of_lt_32 hsourceLeftSsa, labRegisterOfNat_of_lt_32 hsourceRightSsa,
      labRegisterOfNat_of_lt_32 hcarryInSsa, hfreshDestinationBound, hfreshCarryBound,
      hsourceLeftSsa, hsourceRightSsa, hcarryInSsa,
      hfreshDestinationScratch, hfreshCarryScratch,
      hfreshSourceLeftScratch, hfreshSourceRightScratch,
      hfreshCarryInScratch, executeInstructions]
  · have hsource := executeInstructions_addCarry_general source
        ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩
        ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩
        ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩ hsourceZero
        (by intro heq; apply hdestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryNonzero; exact congrArg Fin.val heq)
        (riscvRegisterName_fin_ne hdestination hresultCarry hdestinationDistinct)
        (riscvRegisterName_fin_ne hdestination hsourceRight hdestinationSourceRight)
        (riscvRegisterName_fin_ne_thirtyOne hdestination hdestinationScratch)
        (riscvRegisterName_fin_ne_thirtyOne hresultCarry hresultCarryScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceLeft hsourceLeftScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceRight hsourceRightScratch)
        (riscvRegisterName_fin_ne_thirtyOne hcarryIn hcarryInScratch)
    have htarget := executeInstructions_addCarry_general target
        ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩
        ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩
        ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
        ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩
        ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩ htargetZero
        (by intro heq; apply hfreshDestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryNonzero; exact congrArg Fin.val heq)
        (riscvRegisterName_fin_ne hfreshDestinationBound hfreshCarryBound hfreshDistinct)
        (riscvRegisterName_fin_ne hfreshDestinationBound hsourceRightSsa hfreshDestinationSourceRight)
        (riscvRegisterName_fin_ne_thirtyOne hfreshDestinationBound hfreshDestinationScratch)
        (riscvRegisterName_fin_ne_thirtyOne hfreshCarryBound hfreshCarryScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceLeftSsa hfreshSourceLeftScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceRightSsa hfreshSourceRightScratch)
        (riscvRegisterName_fin_ne_thirtyOne hcarryInSsa hfreshCarryInScratch)
    have hsourceLeftResult := congrArg Prod.fst hsource
    have htargetLeftResult := congrArg Prod.fst htarget
    calc
      readRegister (executeInstructions source sourceCode)
          ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ =
          (addCarryWords (readRegister source ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩)
            (readRegister source ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩)
            (readRegister source ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩)).1 := by
              exact hsourceLeftResult
      _ = (addCarryWords (readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩)
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩)
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩)).1 := by
              rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
      _ = readRegister (executeInstructions target targetCode)
          ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩ := by
              exact htargetLeftResult.symm
  · have hsource := executeInstructions_addCarry_general source
        ⟨riscvRegisterName destination, riscvRegisterName_lt_32 hdestination⟩ ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩
        ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩ ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩
        ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩ hsourceZero
        (by intro heq; apply hdestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hresultCarryNonzero; exact congrArg Fin.val heq)
        (riscvRegisterName_fin_ne hdestination hresultCarry hdestinationDistinct)
        (riscvRegisterName_fin_ne hdestination hsourceRight hdestinationSourceRight)
        (riscvRegisterName_fin_ne_thirtyOne hdestination hdestinationScratch)
        (riscvRegisterName_fin_ne_thirtyOne hresultCarry hresultCarryScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceLeft hsourceLeftScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceRight hsourceRightScratch)
        (riscvRegisterName_fin_ne_thirtyOne hcarryIn hcarryInScratch)
    have htarget := executeInstructions_addCarry_general target
        ⟨riscvRegisterName freshDestination, riscvRegisterName_lt_32 hfreshDestinationBound⟩
        ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩
        ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩
        ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩
        ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩ htargetZero
        (by intro heq; apply hfreshDestinationNonzero; exact congrArg Fin.val heq)
        (by intro heq; apply hfreshCarryNonzero; exact congrArg Fin.val heq)
        (riscvRegisterName_fin_ne hfreshDestinationBound hfreshCarryBound hfreshDistinct)
        (riscvRegisterName_fin_ne hfreshDestinationBound hsourceRightSsa hfreshDestinationSourceRight)
        (riscvRegisterName_fin_ne_thirtyOne hfreshDestinationBound hfreshDestinationScratch)
        (riscvRegisterName_fin_ne_thirtyOne hfreshCarryBound hfreshCarryScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceLeftSsa hfreshSourceLeftScratch)
        (riscvRegisterName_fin_ne_thirtyOne hsourceRightSsa hfreshSourceRightScratch)
        (riscvRegisterName_fin_ne_thirtyOne hcarryInSsa hfreshCarryInScratch)
    have hsourceCarryResult := congrArg Prod.snd hsource
    have htargetCarryResult := congrArg Prod.snd htarget
    calc
      readRegister (executeInstructions source sourceCode)
          ⟨riscvRegisterName resultCarry, riscvRegisterName_lt_32 hresultCarry⟩ =
          (addCarryWords (readRegister source ⟨riscvRegisterName sourceLeft, riscvRegisterName_lt_32 hsourceLeft⟩)
            (readRegister source ⟨riscvRegisterName sourceRight, riscvRegisterName_lt_32 hsourceRight⟩)
            (readRegister source ⟨riscvRegisterName carryIn, riscvRegisterName_lt_32 hcarryIn⟩)).2 := by
              exact hsourceCarryResult
      _ = (addCarryWords (readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceLeft), riscvRegisterName_lt_32 hsourceLeftSsa⟩)
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa sourceRight), riscvRegisterName_lt_32 hsourceRightSsa⟩)
            (readRegister target ⟨riscvRegisterName (wordSsaRead ssa carryIn), riscvRegisterName_lt_32 hcarryInSsa⟩)).2 := by
              rw [hsourceLeftValue, hsourceRightValue, hcarryInValue]
      _ = readRegister (executeInstructions target targetCode)
          ⟨riscvRegisterName freshCarry, riscvRegisterName_lt_32 hfreshCarryBound⟩ := by
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
