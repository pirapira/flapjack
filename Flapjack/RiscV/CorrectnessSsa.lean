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

end Flapjack.RiscV
