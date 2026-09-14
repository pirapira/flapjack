import Flapjack.RiscV.CorrectnessCallEntry
import Flapjack.Test.CorrectnessCalls

/-! Regression coverage for the list-level Loop-to-Word call-entry bridge. -/

namespace Flapjack

def callEntryContext : WordContext :=
  { vars := [(10, 2), (11, 3)] }

def callEntryState : RiscV.State 8 :=
  RiscV.writeRegister
    (RiscV.writeRegister (RiscV.zeroState 8) ⟨RiscV.riscvRegisterName 2, by decide⟩ (BitVec.ofNat 8 17))
    ⟨RiscV.riscvRegisterName 3, by decide⟩ (BitVec.ofNat 8 29)

def callEntryLocals : Nat → Option (RiscV.Word 8)
  | 10 => some (BitVec.ofNat 8 17)
  | 11 => some (BitVec.ofNat 8 29)
  | _ => none

example :
    loopLocalsMappedToRiscV callEntryContext callEntryLocals callEntryState := by
  intro name value hvalue
  by_cases h10 : name = 10
  · subst name
    simp [callEntryLocals] at hvalue
    subst value
    exact ⟨⟨RiscV.riscvRegisterName 2, by decide⟩, by decide, by
      simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
  · by_cases h11 : name = 11
    · subst name
      simp [callEntryLocals] at hvalue
      subst value
      exact ⟨⟨RiscV.riscvRegisterName 3, by decide⟩, by decide, by
        simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
    · have hnone : callEntryLocals name = none := by
        simp [callEntryLocals]
      simp [hnone] at hvalue

example :
    loopReadLocals callEntryLocals [10, 11] =
      some [BitVec.ofNat 8 17, BitVec.ofNat 8 29] := by
  simp [loopReadLocals, callEntryLocals]

example :
    (wordMapVars callEntryContext [10, 11]).mapM (fun name => do
      let register ← RiscV.labRegisterOfNat name
      pure (RiscV.readRegister callEntryState register)) =
        some [BitVec.ofNat 8 17, BitVec.ofNat 8 29] := by
  apply loopReadLocals_wordMapVars_agreement callEntryContext
    { locals := callEntryLocals, globals := fun _ => none, memory := fun _ => none }
    callEntryState [10, 11] [BitVec.ofNat 8 17, BitVec.ofNat 8 29]
  · intro name value hvalue
    by_cases h10 : name = 10
    · subst name
      simp [callEntryLocals] at hvalue
      subst value
      exact ⟨⟨RiscV.riscvRegisterName 2, by decide⟩, by decide, by
        simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
    · by_cases h11 : name = 11
      · subst name
        simp [callEntryLocals] at hvalue
        subst value
        exact ⟨⟨RiscV.riscvRegisterName 3, by decide⟩, by decide, by
          simp [callEntryState, RiscV.readRegister, RiscV.writeRegister]⟩
      · have hnone : callEntryLocals name = none := by
          simp [callEntryLocals]
        simp [hnone] at hvalue
  · simp [loopReadLocals, callEntryLocals]

/-! The generalized handler theorem also discharges the existing concrete
    handler call when its binding witnesses are exposed explicitly. -/
example : loopLocalsMappedToRiscV ({ vars := [] } : WordContext)
    handlerCallFinalLoop.locals handlerCallFinalWord := by
  apply loopToWord_call_handler_simulation_general
    (context := ({ vars := [] } : WordContext))
    (functions := [(1, [10], handlerCallBody)])
    (wordFunctions := [(1, [10],
      loopToWordProg ({ vars := [] } : WordContext) handlerCallBody)])
    (loopState := handlerCallLoopState)
    (wordState := handlerCallWordState)
    (loopHandler := handlerCallLoopHandler)
    (wordHandler := handlerCallWordHandler)
    (target := 1)
    (parameters := [10])
    (arguments := [2])
    (exception := 5)
    (argumentValues := [9])
    (fuel := 2)
    (loopBody := handlerCallBody)
    (handlerBody := .skip)
    (calleeLocals := updateLoopLocal (fun _ => none) 10 9)
    (calleeWord := RiscV.writeRegister
      (RiscV.clearWordRegisters handlerCallWordState) ⟨RiscV.riscvRegisterName 10, by decide⟩ 9)
    (exceptionRegister := 5)
    (finalLoop := handlerCallFinalLoop)
    (finalWord := handlerCallFinalWord)
    (hlookupLoop := by simp [lookupLoopFunction, handlerCallBody])
    (hlookupWord := by simp [RiscV.lookupWordFunction, loopToWordProg,
      handlerCallBody, wordFindVar, wordMapVars, lookupNatInfo, wordCompileExp])
    (hread := by simp [loopReadLocals, handlerCallLoopState])
    (hloopBind := by simp [loopBindParameters])
    (hwordBind := by simp [RiscV.bindWordRegisters, RiscV.clearWordRegisters,
      handlerCallWordState, wordMapVars, wordFindVar, lookupNatInfo,
      RiscV.writeRegister, RiscV.registerOfNat, RiscV.riscvRegisterName])
    (hcalleeZero := by
      simp [RiscV.clearWordRegisters, RiscV.writeRegister,
        RiscV.readRegister])
    (hexception := by decide)
    (hexception_nonzero := by decide)
    (hnoalias := by
      intro name hname register hregister
      intro heq
      have hname' : name = 5 := by
        have hriscv : RiscV.riscvRegisterName name = 5 := by
          have hsame : RiscV.labRegisterOfNat name = some register := by
            simpa [wordFindVar, lookupNatInfo] using hregister
          have hsame' : RiscV.registerOfNat (RiscV.riscvRegisterName name) = some register := by
            simpa [RiscV.labRegisterOfNat, RiscV.riscvRegisterName] using hsame
          have hfive : RiscV.registerOfNat 5 = some (5 : Fin 32) := by decide
          exact RiscV.registerOfNat_injective hsame' hfive heq
        exact RiscV.riscvRegisterName_injective_lt_32
          (RiscV.lt_32_of_riscvRegisterName_lt_32 (by rw [hriscv]; decide))
          (by decide) hriscv
      exact hname hname')
    (hbody := by
      intro calleeLoop calleeWord loopResult wordResult hzero hloop hword
      change calleeWord.registers 0 = 0 at hzero
      simp [handlerCallBody, loopToWordProg, wordCompileExp,
        wordFindVar, lookupNatInfo,
        evalLoopProgWithCallsAndFfi, evalLoopProg,
        evalLoopExp, updateLoopLocal,
        RiscV.evalWordFunctionWithHandlersAndFfi, RiscV.evalWordFunction,
        RiscV.wordExpToInstructions,
        RiscV.wordExpToInstruction,
        RiscV.executeInstructions, RiscV.execute, RiscV.nextPc,
        RiscV.labRegisterOfNat, RiscV.readRegister, RiscV.writeRegister, hzero] at hloop hword
      cases hloop
      cases hword
      simp [loopCallBodyResultCompatible, RiscV.writeRegister, RiscV.execute,
        RiscV.readRegister, hzero])
    (hhandler := by
      intro exceptionValue handlerWord handlerLoop handlerFinalWord handlerState
        hstate hlocals hloop hword
      have hloop' :
          some (LoopResult.normal handlerState) =
            some (LoopResult.normal handlerLoop) := by
        simpa [evalLoopProgWithCallsAndFfi, evalLoopProg] using hloop
      have hword' :
          some (RiscV.WordControlResult.normal handlerWord) =
            some (RiscV.WordControlResult.normal handlerFinalWord) := by
        simpa [RiscV.evalWordFunctionWithHandlersAndFfi,
          RiscV.evalWordFunction, loopToWordProg] using hword
      injection hloop' with hloopResult
      injection hword' with hwordResult
      cases hloopResult
      cases hwordResult
      simpa [hstate] using hlocals)
    (hlocals := handlerCall_mappedLocals)
  · simp [evalLoopCallWithCallsAndFfi, evalLoopProgWithCallsAndFfi,
      evalLoopProg, evalLoopExp, loopReadLocals, loopBindParameters,
      lookupLoopFunction, handlerCallBody, handlerCallLoopState,
      handlerCallFinalLoop, updateLoopLocal]
  · simp [RiscV.evalWordCallWithHandlersAndFfi, RiscV.lookupWordFunction,
      wordMapVars, wordFindVar, lookupNatInfo, RiscV.readWordRegisters,
      RiscV.bindWordRegisters, List.foldl, List.zip,
      RiscV.clearWordRegisters, handlerCallBody,
      handlerCallWordState, handlerCallFinalWord, loopToWordProg,
      wordCompileExp, wordFindVar, lookupNatInfo,
      RiscV.evalWordFunctionWithHandlersAndFfi, RiscV.evalWordFunction,
      RiscV.wordExpToInstructions,
      RiscV.wordExpToInstruction,
      RiscV.executeInstructions, RiscV.execute, RiscV.nextPc,
      RiscV.registerOfNat, RiscV.riscvRegisterName, RiscV.readRegister,
      RiscV.writeRegister]

end Flapjack
