import Flapjack.Correctness

namespace Flapjack

def memoryCorrectnessContext : WordContext :=
  { vars := [(1, 3), (2, 2)] }

def memoryCorrectnessLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun name => if name = 1 then some (BitVec.ofNat 64 16) else none
    globals := fun _ => none
    memory := fun address =>
      if address = BitVec.ofNat 64 16 then some (BitVec.ofNat 64 42) else none }

def memoryCorrectnessWordState : RiscV.State 64 :=
  RiscV.writeRegister
    (RiscV.writeWord32 (RiscV.zeroState 64) (BitVec.ofNat 64 16)
      (BitVec.ofNat 64 42)) 3 (BitVec.ofNat 64 16)

theorem memoryCorrectness_mappedLocals :
    loopLocalsMappedToRiscV memoryCorrectnessContext
      memoryCorrectnessLoopState.locals memoryCorrectnessWordState := by
  intro name value hvalue
  by_cases hname : name = 1
  · subst name
    simp [memoryCorrectnessLoopState] at hvalue
    subst value
    refine ⟨3, ?_, ?_⟩
    · native_decide
    · simp [memoryCorrectnessWordState, RiscV.writeRegister,
        RiscV.readRegister]
  · simp [memoryCorrectnessLoopState, hname] at hvalue

theorem memoryCorrectness_noalias :
    ∀ name, name ≠ 2 →
      ∀ register,
        RiscV.registerOfNat (wordFindVar memoryCorrectnessContext name) =
          some register → register ≠ 2 := by
  intro name hname register hregister heq
  have htwo : RiscV.registerOfNat 2 = some (2 : Fin 32) := by
    native_decide
  have hfind := RiscV.registerOfNat_injective hregister htwo heq
  by_cases hname_one : name = 1
  · subst name
    simp [memoryCorrectnessContext, wordFindVar, lookupNatInfo] at hfind
  · by_cases hname_two : name = 2
    · exact (hname hname_two).elim
    · simp [memoryCorrectnessContext, wordFindVar, lookupNatInfo,
        hname_one, hname_two, Ne.symm hname_one, Ne.symm hname_two] at hfind

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext (.load32 1 2)) =
          some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        (updateLoopLocal memoryCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 42)) resultState := by
  apply loopToWord_load32_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (destination := 2) (destinationRegister := 2)
    (addressValue := BitVec.ofNat 64 16)
    (value := BitVec.ofNat 64 42)
    (zero := by
      change memoryCorrectnessWordState.registers (0 : Fin 32) = 0
      simp [memoryCorrectnessWordState, RiscV.writeRegister,
        RiscV.zeroState, RiscV.writeWord32, RiscV.writeByte])
    (hlocals := by
      intro name value hvalue
      by_cases hname : name = 1
      · subst name
        simp [memoryCorrectnessLoopState] at hvalue
        subst value
        refine ⟨3, ?_, ?_⟩
        · native_decide
        · simp [memoryCorrectnessWordState, RiscV.writeRegister,
            RiscV.readRegister]
      · simp [memoryCorrectnessLoopState, hname] at hvalue)
    (haddress := by simp [memoryCorrectnessLoopState])
    (hmemory := by simp [memoryCorrectnessLoopState])
    (hmachine := by native_decide)
    (hdestination := by native_decide)
    (hdestination_nonzero := by decide)
    (hnoalias := by
      intro name hname register hregister
      have htwo : RiscV.registerOfNat 2 = some (2 : Fin 32) := by
        native_decide
      intro heq
      have hfind := RiscV.registerOfNat_injective hregister htwo heq
      by_cases hname_one : name = 1
      · subst name
        simp [memoryCorrectnessContext, wordFindVar, lookupNatInfo] at hfind
      · by_cases hname_two : name = 2
        · exact (hname hname_two).elim
        · simp [memoryCorrectnessContext, wordFindVar, lookupNatInfo,
            hname_one, hname_two, Ne.symm hname_one, Ne.symm hname_two] at hfind
          )

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext (.loadByte 1 2)) =
          some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        (updateLoopLocal memoryCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 (BitVec.ofNat 8 42).toNat)) resultState := by
  apply loopToWord_loadByte_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (destination := 2) (destinationRegister := 2)
    (addressValue := BitVec.ofNat 64 16)
    (byteValue := BitVec.ofNat 8 42)
    (zero := by
      change memoryCorrectnessWordState.registers (0 : Fin 32) = 0
      simp [memoryCorrectnessWordState, RiscV.writeRegister,
        RiscV.zeroState, RiscV.writeWord32, RiscV.writeByte])
    (hlocals := memoryCorrectness_mappedLocals)
    (haddress := by simp [memoryCorrectnessLoopState])
    (hmemory := by native_decide)
    (hmachine := by native_decide)
    (hdestination := by native_decide)
    (hdestination_nonzero := by decide)
    (hnoalias := memoryCorrectness_noalias)

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext (.storeByte 1 1)) =
          some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        memoryCorrectnessLoopState.locals resultState := by
  apply loopToWord_storeByte_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (value := 1)
    (addressRegister := 3) (valueRegister := 3)
    (haddress := by native_decide)
    (hvalue := by native_decide)
    (hlocals := memoryCorrectness_mappedLocals)

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext
          (.shMem .load8 2 (.var 1))) = some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        (updateLoopLocal memoryCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 (BitVec.ofNat 8 42).toNat)) resultState := by
  apply loopToWord_shMem_load8_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (destination := 2) (destinationRegister := 2)
    (addressValue := BitVec.ofNat 64 16)
    (byteValue := BitVec.ofNat 8 42)
    (zero := by
      change memoryCorrectnessWordState.registers (0 : Fin 32) = 0
      simp [memoryCorrectnessWordState, RiscV.writeRegister,
        RiscV.zeroState, RiscV.writeWord32, RiscV.writeByte])
    (hlocals := memoryCorrectness_mappedLocals)
    (haddress := by simp [memoryCorrectnessLoopState])
    (hmemory := by native_decide)
    (hmachine := by native_decide)
    (hdestination := by native_decide)
    (hdestination_nonzero := by decide)
    (hnoalias := memoryCorrectness_noalias)

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext
          (.shMem .store8 1 (.var 1))) = some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        memoryCorrectnessLoopState.locals resultState := by
  apply loopToWord_shMem_store8_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (value := 1)
    (addressRegister := 3) (valueRegister := 3)
    (haddress := by native_decide)
    (hvalue := by native_decide)
    (hlocals := memoryCorrectness_mappedLocals)

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext
          (.shMem .load16 2 (.var 1))) = some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        (updateLoopLocal memoryCorrectnessLoopState.locals 2
          (BitVec.ofNat 64 42)) resultState := by
  apply loopToWord_shMem_load16_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (destination := 2) (destinationRegister := 2)
    (addressValue := BitVec.ofNat 64 16)
    (value := BitVec.ofNat 64 42)
    (zero := by
      change memoryCorrectnessWordState.registers (0 : Fin 32) = 0
      simp [memoryCorrectnessWordState, RiscV.writeRegister,
        RiscV.zeroState, RiscV.writeWord32, RiscV.writeByte])
    (hlocals := memoryCorrectness_mappedLocals)
    (haddress := by simp [memoryCorrectnessLoopState])
    (hmemory := by native_decide)
    (hmachine := by native_decide)
    (hdestination := by native_decide)
    (hdestination_nonzero := by decide)
    (hnoalias := memoryCorrectness_noalias)

example :
    ∀ resultState,
      RiscV.evalWordProg memoryCorrectnessWordState
        (loopToWordProg memoryCorrectnessContext
          (.shMem .store16 1 (.var 1))) = some resultState →
      loopLocalsMappedToRiscV memoryCorrectnessContext
        memoryCorrectnessLoopState.locals resultState := by
  apply loopToWord_shMem_store16_preserves_mapped_locals
    (context := memoryCorrectnessContext)
    (loopState := memoryCorrectnessLoopState)
    (state := memoryCorrectnessWordState)
    (address := 1) (value := 1)
    (addressRegister := 3) (valueRegister := 3)
    (haddress := by native_decide)
    (hvalue := by native_decide)
    (hlocals := memoryCorrectness_mappedLocals)

end Flapjack
