import Flapjack.RiscV.CorrectnessFfi

/-!
Regression for an exception raised by a callee and resumed by a handler at a
loop-aware call boundary.  The callee raises its parameter, and the handler
is the identity program; the exception binding must be visible in both
mapped-local states.
-/

namespace Flapjack

open RiscV

def loopCallHandlerLoopState : LoopState (Word 64) :=
  { locals := fun name => if name = 2 then some (BitVec.ofNat 64 9) else none
    globals := fun _ => none
    memory := fun _ => none }

def loopCallHandlerWordState : State 64 :=
  writeRegister (zeroState 64) ⟨riscvRegisterName 2, by decide⟩ 9

def loopCallHandlerBody : LoopProg (Word 64) :=
  .raise 10

def loopCallHandlerHandler : LoopProg (Word 64) :=
  .skip

theorem loopCallHandler_mapped_locals :
    loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
      loopCallHandlerLoopState.locals loopCallHandlerWordState := by
  intro name value hvalue
  by_cases hname : name = 2
  · subst name
    refine ⟨⟨riscvRegisterName 2, by decide⟩, by decide, ?_⟩
    simpa [loopCallHandlerLoopState, loopCallHandlerWordState,
      readRegister, writeRegister] using hvalue
  · simp [loopCallHandlerLoopState, hname] at hvalue

theorem loopCallHandler_simulation :
    loopResultMappedToWordLoop ({ vars := [] } : WordContext)
      (.normal { loopCallHandlerLoopState with
        locals := updateLoopLocal loopCallHandlerLoopState.locals 11 9 })
      (.normal (writeRegister loopCallHandlerWordState ⟨riscvRegisterName 11, by decide⟩ 9)) := by
  apply loopToWord_call_loop_control_simulation_single_parameter_with_handler
    (context := ({ vars := [] } : WordContext))
    (primitive := fun _ _ => none)
    (functions := [(1, [10], loopCallHandlerBody)])
    (wordFunctions := [(1, [10], loopToWordProg
      ({ vars := [] } : WordContext) loopCallHandlerBody)])
    (loopState := loopCallHandlerLoopState)
    (wordState := loopCallHandlerWordState)
    (loopHandler := fun _ _ _ _ _ state => some state)
    (wordHandler := fun _ _ _ _ _ state => some state)
    (target := 1)
    (parameter := 10)
    (argument := 2)
    (exception := 11)
    (argumentValue := BitVec.ofNat 64 9)
    (fuel := 3)
    (loopBody := loopCallHandlerBody)
    (handlerBody := loopCallHandlerHandler)
    (parameterRegister := ⟨riscvRegisterName 10, by decide⟩)
    (exceptionRegister := ⟨riscvRegisterName 11, by decide⟩)
    (loopResult := .normal { loopCallHandlerLoopState with
      locals := updateLoopLocal loopCallHandlerLoopState.locals 11 9 })
    (wordResult := .normal (writeRegister loopCallHandlerWordState ⟨riscvRegisterName 11, by decide⟩ 9))
    (hlookupLoop := by simp [lookupLoopFunction, loopCallHandlerBody])
    (hlookupWord := by simp [lookupWordFunction, wordFindVar, lookupNatInfo,
      loopToWordProg, loopCallHandlerBody])
    (hparameter := by decide)
    (hparameter_nonzero := by decide)
    (hexception := by decide)
    (hexception_nonzero := by decide)
    (hargument := by simp [loopCallHandlerLoopState])
    (hnoalias := by
      intro name hname register hregister
      intro heq
      have hname' : name = 11 := by
        have hriscv : riscvRegisterName name = riscvRegisterName 11 := by
          have hsame : RiscV.labRegisterOfNat name = some register := by
            simpa [wordFindVar, lookupNatInfo] using hregister
          have hsame' : RiscV.registerOfNat (riscvRegisterName name) = some register := by
            simpa [RiscV.labRegisterOfNat] using hsame
          have h11 : RiscV.registerOfNat (riscvRegisterName 11) =
              some (⟨riscvRegisterName 11, by decide⟩ : Fin 32) := by decide
          exact RiscV.registerOfNat_injective hsame' h11 heq
        exact riscvRegisterName_injective_lt_32
          (RiscV.lt_32_of_riscvRegisterName_lt_32 (by rw [hriscv]; decide))
          (by decide) hriscv
      exact hname hname')
    (hbody := by
      intro calleeLoop calleeWord bodyResult bodyWordResult hcallee hloop hword
      cases hconfig : calleeLoop.locals 10 with
      | none =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
            loopCallHandlerBody, hconfig] at hloop
      | some exceptionValue =>
          have hloop' :
              some (.raised calleeLoop exceptionValue) = some bodyResult := by
            simpa [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
              loopCallHandlerBody, hconfig] using hloop
          have hword' :
              some (.raised calleeWord
                (readRegister calleeWord ⟨riscvRegisterName 10, by decide⟩)) =
                some bodyWordResult := by
            simpa [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
              loopCallHandlerBody, RiscV.labRegisterOfNat, RiscV.registerOfNat,
              wordFindVar, lookupNatInfo] using hword
          cases hloop'
          cases hword'
          rcases hcallee 10 exceptionValue hconfig with
            ⟨register, hregister, hvalue⟩
          have hregister' : register = ⟨riscvRegisterName 10, by decide⟩ := by
            have h10 : RiscV.labRegisterOfNat 10 =
                some (⟨riscvRegisterName 10, by decide⟩ : Fin 32) := by
              decide
            exact Option.some.inj (hregister.symm.trans h10)
          subst register
          exact ⟨hcallee, hvalue⟩)
    (hhandler := by
      intro exceptionValue handlerLoopState handlerWordState handlerResult handlerWordResult
        hstate hlocals hloop hword
      have hloop' :
          some (.normal handlerLoopState) = some handlerResult := by
        simpa [evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
          loopCallHandlerHandler] using hloop
      have hword' : some (.normal handlerWordState) = some handlerWordResult := by
        simpa [loopToWordProg, RiscV.evalWordLoopProgWithHandlersAndFfi,
          RiscV.evalWordFunction, loopCallHandlerHandler] using hword
      cases hloop'
      cases hword'
      simpa [loopResultMappedToWordLoop, hstate] using hlocals)
    (hlocals := loopCallHandler_mapped_locals)
    (hloop := by
      simp [evalLoopCallWithPrimitiveCallsAndFfi,
        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
        lookupLoopFunction, loopCallHandlerBody, loopCallHandlerHandler,
        loopCallHandlerLoopState, loopReadLocals, loopBindParameters,
        updateLoopLocal])
    (hword := by
      simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
        RiscV.evalWordLoopProgWithHandlersAndFfi, RiscV.lookupWordFunction,
        loopToWordProg, loopCallHandlerBody, loopCallHandlerHandler,
        loopCallHandlerWordState, writeRegister, readRegister,
        RiscV.readWordRegisters, RiscV.bindWordRegisters,
        RiscV.clearWordRegisters, wordFindVar, lookupNatInfo,
        RiscV.evalWordFunction])

end Flapjack
