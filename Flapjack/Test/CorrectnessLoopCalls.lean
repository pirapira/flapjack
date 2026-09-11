import Flapjack.RiscV.CorrectnessFfi

/-!
Regression for a loop-control result crossing a handler-free call boundary.
The callee immediately breaks, so the caller must receive the same break
label and the caller's mapped locals must remain intact.
-/

namespace Flapjack

open RiscV

def loopCallControlLoopState : LoopState (Word 64) :=
  { locals := fun name => if name = 2 then some (BitVec.ofNat 64 9) else none
    globals := fun _ => none
    memory := fun _ => none }

def loopCallControlWordState : State 64 :=
  writeRegister (zeroState 64) 2 9

theorem loopCallControl_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      loopCallControlLoopState.locals loopCallControlWordState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    refine ⟨2, by decide, ?_⟩
    simpa [loopCallControlLoopState, loopCallControlWordState,
      readRegister, writeRegister] using hvalue
  · simp [loopCallControlLoopState, hname] at hvalue

theorem loopCallControl_break_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.broke loopCallControlLoopState 0)
      (.broke loopCallControlWordState 0) := by
  apply loopToWord_call_loop_control_simulation_single_parameter
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], (.break 0 : LoopProg (Word 64)))])
    (wordFunctions := [(1, [10], (.break 0 : WordProg (Word 64)))])
    (loopState := loopCallControlLoopState)
    (wordState := loopCallControlWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (argumentValue := BitVec.ofNat 64 9)
    (fuel := 3)
    (loopBody := (.break 0 : LoopProg (Word 64)))
    (parameterRegister := 10)
    (loopResult := .broke loopCallControlLoopState 0)
    (wordResult := .broke loopCallControlWordState 0)
    (hlookupLoop := by simp [lookupLoopFunction])
    (hlookupWord := by simp [lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg])
    (hparameter := by decide)
    (hparameter_nonzero := by decide)
    (hargument := by simp [loopCallControlLoopState])
    (hbody := by
      intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
      cases bodyResult <;> cases bodyWordResult <;>
        simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
          loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi] at hloop hword ⊢ <;>
        rcases hloop with ⟨rfl, rfl⟩ <;>
        rcases hword with ⟨rfl, rfl⟩ <;>
        exact ⟨rfl, hcallee⟩)
    (hlocals := loopCallControl_mapped_locals)
    (hloop := by
      simp [evalLoopCallWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
        lookupLoopFunction, loopCallControlLoopState, loopReadLocals,
        loopBindParameters])
    (hword := by
      simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
        loopCallControlWordState, writeRegister,
        readRegister, RiscV.readWordRegisters, RiscV.bindWordRegisters,
        RiscV.clearWordRegisters, registerOfNat, wordFindVar, lookupNatInfo])

def loopCallFfiBody : LoopProg (Word 64) :=
  .ffi "identity" 10 10 10 10 []

theorem loopCallFfi_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.normal loopCallControlLoopState)
      (.normal loopCallControlWordState) := by
  apply loopToWord_call_loop_control_simulation_single_parameter
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], loopCallFfiBody)])
    (wordFunctions := [(1, [10], loopToWordProg
      ({ vars := [] } : WordContext) loopCallFfiBody)])
    (loopState := loopCallControlLoopState)
    (wordState := loopCallControlWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (argumentValue := BitVec.ofNat 64 9)
    (fuel := 3)
    (loopBody := loopCallFfiBody)
    (parameterRegister := 10)
    (loopResult := .normal loopCallControlLoopState)
    (wordResult := .normal loopCallControlWordState)
    (hlookupLoop := by simp [lookupLoopFunction, loopCallFfiBody])
    (hlookupWord := by simp [lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg, loopCallFfiBody])
    (hparameter := by decide)
    (hparameter_nonzero := by decide)
    (hargument := by simp [loopCallControlLoopState])
    (hbody := by
      intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
      cases bodyResult with
      | normal loopResult =>
          cases bodyWordResult with
          | normal wordResult =>
              exact loopToWord_ffi_loop_simulation
                (context := ({ vars := [] } : WordContext))
                (primitive := fun _ _ => none)
                (functions := [(1, [10], loopCallFfiBody)])
                (wordFunctions := [(1, [10], loopToWordProg
                  ({ vars := [] } : WordContext) loopCallFfiBody)])
                (loopState := calleeLoop)
                (wordState := calleeWord)
                (loopHandler := fun _ _ _ _ _ state => some state)
                (wordHandler := fun _ _ _ _ _ state => some state)
                (handler_agrees := by
                  intro function configuration configurationLength array arrayLength
                    loopInput wordInput loopOutput wordOutput hlocals hloop hword
                  simp at hloop hword
                  cases hloop
                  cases hword
                  exact hlocals)
                (function := "identity")
                (configuration := 10)
                (configurationLength := 10)
                (array := 10)
                (arrayLength := 10)
                (live := [])
                (fuel := 2)
                (hlocals := hcallee)
                loopResult wordResult hloop hword
          | returned wordState values =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | raised wordState exception =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | broke wordState label =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
          | continued wordState label =>
              simp [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
                loopCallFfiBody, registerOfNat, wordFindVar, lookupNatInfo] at hword
      | returned loopState values =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | raised loopState exception =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | broke loopState label =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop
      | continued loopState label =>
          cases hconfig : calleeLoop.locals 10 <;>
            simp [evalLoopProgWithPrimitiveCallsAndFfi,
              loopCallFfiBody, hconfig] at hloop)
    (hlocals := loopCallControl_mapped_locals)
    (hloop := by
      simp [evalLoopCallWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, 
        lookupLoopFunction, loopCallFfiBody, loopCallControlLoopState,
        loopReadLocals, loopBindParameters, updateLoopLocal])
    (hword := by
      simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
        loopToWordProg, loopCallFfiBody, loopCallControlWordState,
        writeRegister, readRegister, RiscV.readWordRegisters,
        RiscV.bindWordRegisters, RiscV.clearWordRegisters,
        registerOfNat, wordFindVar, lookupNatInfo])

def loopCallHandlerFfiBody : LoopProg (Word 64) :=
  .ffi "identity" 10 10 10 10 []

def loopCallHandlerFfiLoopState : LoopState (Word 64) :=
  { locals := fun name =>
      if name = 2 then some (BitVec.ofNat 64 9)
      else if name = 10 then some (BitVec.ofNat 64 9)
      else none
    globals := fun _ => none
    memory := fun _ => none }

def loopCallHandlerFfiWordState : State 64 :=
  writeRegister
    (writeRegister (zeroState 64) 2 (BitVec.ofNat 64 9)) 10
      (BitVec.ofNat 64 9)

def loopCallHandlerFfiLoopHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    LoopState (Word 64) → Option (LoopState (Word 64)) :=
  fun _ _ _ _ _ state => some state

def loopCallHandlerFfiWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun _ _ _ _ _ state => some state

theorem loopCall_handler_ffi_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      loopCallHandlerFfiLoopState.locals loopCallHandlerFfiWordState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    refine ⟨2, by decide, ?_⟩
    simpa [loopCallHandlerFfiLoopState, loopCallHandlerFfiWordState,
      readRegister, writeRegister] using hvalue
  · by_cases hname10 : name = 10
    · subst name
      refine ⟨10, by decide, ?_⟩
      simpa [loopCallHandlerFfiLoopState, loopCallHandlerFfiWordState,
        readRegister, writeRegister] using hvalue
    · simp [loopCallHandlerFfiLoopState, hname, hname10] at hvalue

theorem loopCall_handler_ffi_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.normal { loopCallHandlerFfiLoopState with
        locals := updateLoopLocal loopCallHandlerFfiLoopState.locals 8 9 })
      (.normal (writeRegister loopCallHandlerFfiWordState 8 9)) := by
  apply loopToWord_call_loop_control_simulation_single_parameter_with_handler
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], (.raise 10 : LoopProg (Word 64)))])
    (wordFunctions := [(1, [10], (.raise 10 : WordProg (Word 64)))])
    (loopState := loopCallHandlerFfiLoopState)
    (wordState := loopCallHandlerFfiWordState)
    (loopHandler := loopCallHandlerFfiLoopHandler)
    (wordHandler := loopCallHandlerFfiWordHandler)
    (target := 1) (parameter := 10) (argument := 2) (exception := 8)
    (argumentValue := BitVec.ofNat 64 9) (fuel := 4)
    (loopBody := (.raise 10 : LoopProg (Word 64)))
    (handlerBody := loopCallHandlerFfiBody)
    (parameterRegister := 10) (exceptionRegister := 8)
    (loopResult := .normal { loopCallHandlerFfiLoopState with
      locals := updateLoopLocal loopCallHandlerFfiLoopState.locals 8 9 })
    (wordResult := .normal (writeRegister loopCallHandlerFfiWordState 8 9))
  · simp [lookupLoopFunction]
  · simp [RiscV.lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg]
  · decide
  · decide
  · decide
  · decide
  · simp [loopCallHandlerFfiLoopState]
  · intro name hname register hregister
    by_cases hname2 : name = 2
    · subst name
      have hregister' : register = 2 := by
        simpa [wordFindVar, lookupNatInfo, registerOfNat] using hregister.symm
      simp [hregister']
    · by_cases hname10 : name = 10
      · subst name
        have hregister' : register = 10 := by
          simpa [wordFindVar, lookupNatInfo, registerOfNat] using hregister.symm
        simp [hregister']
      · by_cases hname8 : name = 8
        · exact (hname hname8).elim
        · simp [wordFindVar, lookupNatInfo] at hregister ⊢
          intro hregister8
          exact hname8 (registerOfNat_injective hregister (by decide) hregister8)
  · intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
    cases hvalue : calleeLoop.locals 10 with
    | none =>
        simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, hvalue] at hloop
    | some value =>
        have hloop' : some (.raised calleeLoop value) = some bodyResult := by
          simpa [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, hvalue] using hloop
        cases hloop'
        have hword' :
            some (.raised calleeWord (readRegister calleeWord 10)) =
              some bodyWordResult := by
          simpa [RiscV.evalWordLoopProgWithHandlersAndFfi, loopToWordProg,
            wordFindVar, lookupNatInfo, registerOfNat] using hword
        cases hword'
        rcases hcallee 10 value hvalue with ⟨register, hregister, hvalue'⟩
        have hregister' : register = 10 := by
          simpa [wordFindVar, lookupNatInfo, registerOfNat] using hregister.symm
        subst register
        exact ⟨hcallee, hvalue'⟩
  · intro exceptionValue handlerLoopState handlerWordState handlerResult
      handlerWordResult hhandlerLocalsEq hhandlerLocals hhandlerLoop hhandlerWord
    have hhandlerLocals' :
        loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
          handlerLoopState.locals handlerWordState := by
      simpa [hhandlerLocalsEq] using hhandlerLocals
    cases handlerResult with
    | normal handlerOutput =>
        cases handlerWordResult with
        | normal handlerWordOutput =>
            exact loopToWord_ffi_loop_simulation
              (context := ({ vars := [] } : WordContext))
              (primitive := fun _ _ => none)
              (functions := [(1, [10], (.raise 10 : LoopProg (Word 64)))])
              (wordFunctions := [(1, [10], (.raise 10 : WordProg (Word 64)))])
              (loopState := handlerLoopState) (wordState := handlerWordState)
              (loopHandler := loopCallHandlerFfiLoopHandler)
              (wordHandler := loopCallHandlerFfiWordHandler)
              (handler_agrees := by
                intro function configuration configurationLength array arrayLength
                  loopInput wordInput loopOutput wordOutput hlocals hloop hword
                simp [loopCallHandlerFfiLoopHandler, loopCallHandlerFfiWordHandler] at hloop hword
                cases hloop
                cases hword
                exact hlocals)
              (function := "identity") (configuration := 10)
              (configurationLength := 10) (array := 10) (arrayLength := 10)
              (live := []) (fuel := 3) (hlocals := hhandlerLocals')
              handlerOutput handlerWordOutput hhandlerLoop hhandlerWord
        | returned _ _ | raised _ _ | broke _ _ | continued _ _ =>
            simp [RiscV.evalWordLoopProgWithHandlersAndFfi, loopToWordProg,
              loopCallHandlerFfiBody, loopCallHandlerFfiWordHandler,
              registerOfNat, wordFindVar, lookupNatInfo] at hhandlerWord
    | returned _ _ | raised _ _ | broke _ _ | continued _ _ =>
        cases hconfiguration : handlerLoopState.locals 10 <;>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfiguration,
            loopCallHandlerFfiBody, loopCallHandlerFfiLoopHandler] at hhandlerLoop
  · exact loopCall_handler_ffi_mapped_locals
  · simp [evalLoopCallWithPrimitiveCallsAndFfi,
      evalLoopProgWithPrimitiveCallsAndFfi, loopCallHandlerFfiLoopHandler,
      loopCallHandlerFfiLoopState, loopCallHandlerFfiBody, lookupLoopFunction,
      loopReadLocals, loopBindParameters, updateLoopLocal, evalLoopProg]
  · simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
      RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
      loopToWordProg, loopCallHandlerFfiBody, loopCallHandlerFfiWordHandler,
      loopCallHandlerFfiWordState, writeRegister, readRegister,
      RiscV.readWordRegisters, RiscV.bindWordRegisters,
      RiscV.clearWordRegisters, registerOfNat, wordFindVar, lookupNatInfo]

end Flapjack
