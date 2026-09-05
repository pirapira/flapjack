import Flapjack.RiscV.CorrectnessFfi

namespace Flapjack

open RiscV

def ffiIdentityLoopState : LoopState (Word 64) :=
  { locals := fun name =>
      if name = 1 then some (BitVec.ofNat 64 10)
      else if name = 2 then some (BitVec.ofNat 64 1)
      else if name = 3 then some (BitVec.ofNat 64 20)
      else if name = 4 then some (BitVec.ofNat 64 2)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def ffiIdentityWordState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 1 10) 2 1) 3 20) 4 2

def ffiIdentityLoopHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun _ _ _ _ _ state => some state

def ffiIdentityWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun _ _ _ _ _ state => some state

example : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    ffiIdentityLoopState.locals ffiIdentityWordState := by
  apply loopToWord_ffi_single_simulation
    ({ vars := [] } : WordContext)
    ffiIdentityLoopState ffiIdentityWordState
    ffiIdentityLoopHandler ffiIdentityWordHandler
    (by
      intro function configuration configurationLength array arrayLength
        loopInput wordInput loopOutput wordOutput hlocals hloop hword
      simp [ffiIdentityLoopHandler, ffiIdentityWordHandler] at hloop hword
      cases hloop
      cases hword
      exact hlocals)
    "identity" 1 2 3 4 []
    (by
      intro name value hvalue
      by_cases h1 : name = 1
      · subst name
        refine ⟨1, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
        simpa [ffiIdentityLoopState, ffiIdentityWordState,
          readRegister, writeRegister] using hvalue
      · by_cases h2 : name = 2
        · subst name
          refine ⟨2, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
          simpa [ffiIdentityLoopState, ffiIdentityWordState,
            readRegister, writeRegister] using hvalue
        · by_cases h3 : name = 3
          · subst name
            refine ⟨3, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
            simpa [ffiIdentityLoopState, ffiIdentityWordState,
              readRegister, writeRegister] using hvalue
          · by_cases h4 : name = 4
            · subst name
              refine ⟨4, by simp [registerOfNat, wordFindVar, lookupNatInfo], ?_⟩
              simpa [ffiIdentityLoopState, ffiIdentityWordState,
                readRegister, writeRegister] using hvalue
            · simp [ffiIdentityLoopState, h1, h2, h3, h4] at hvalue)
  · simp [evalLoopFfi, ffiIdentityLoopHandler, ffiIdentityLoopState]
  · simp [loopToWordProg, evalWordFfi, ffiIdentityWordHandler,
      registerOfNat, wordFindVar, lookupNatInfo, writeRegister,
      readRegister]

end Flapjack
