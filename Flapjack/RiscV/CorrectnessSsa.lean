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

end Flapjack.RiscV
