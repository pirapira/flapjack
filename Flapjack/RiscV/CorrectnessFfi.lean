import Flapjack.Correctness

/-!
Simulation boundary for foreign calls.

The RISC-V model cannot determine the effect of an external function.  This
file therefore states the exact contract needed by `loop_to_word`: whenever
the Loop-side and Word-side host handlers agree on their four arguments and
start from related states, their resulting states remain related.  Under
that contract, the one-step FFI evaluators agree on all mapped locals.
-/

namespace Flapjack.RiscV

theorem loopToWord_ffi_single_simulation [NeZero width]
    (context : WordContext)
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopFfi loopHandler 1 loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFfi wordHandler 1 wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (wordResult, []) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none => simp [evalLoopFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none => simp [evalLoopFfi, hconfig, hconfigLength, harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none => simp [evalLoopFfi, hconfig, hconfigLength, harray, harrayLength] at hloop
              | some arrayLengthValue =>
                  rcases hlocals configuration configurationValue hconfig with
                    ⟨configurationRegister, hconfigurationRegister, hconfigurationValue⟩
                  rcases hlocals configurationLength configurationLengthValue hconfigLength with
                    ⟨configurationLengthRegister, hconfigurationLengthRegister,
                      hconfigurationLengthValue⟩
                  rcases hlocals array arrayValue harray with
                    ⟨arrayRegister, harrayRegister, harrayValue⟩
                  rcases hlocals arrayLength arrayLengthValue harrayLength with
                    ⟨arrayLengthRegister, harrayLengthRegister, harrayLengthValue⟩
                  have hloop' :
                      (loopHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue loopState).bind
                        (fun state => some (LoopResult.normal state)) =
                        some (LoopResult.normal loopResult) := by
                    simpa [evalLoopFfi, hconfig, hconfigLength, harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state => some (state, ([] : List (Word width)))) =
                        some (wordResult, ([] : List (Word width))) := by
                    simpa [loopToWordProg, evalWordFfi,
                      hconfigurationRegister, hconfigurationLengthRegister,
                      harrayRegister, harrayLengthRegister,
                      hconfigurationValue, hconfigurationLengthValue,
                      harrayValue, harrayLengthValue] using hword
                  cases hloopHandler : loopHandler function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue loopState with
                  | none => simp [hloopHandler] at hloop'
                  | some loopOutput =>
                      cases hwordHandler : wordHandler function configurationValue
                          configurationLengthValue arrayValue arrayLengthValue wordState with
                      | none => simp [hwordHandler] at hword'
                      | some wordOutput =>
                          have hloopOutput : loopResult = loopOutput := by
                            simpa [hloopHandler] using hloop'.symm
                          have hwordOutput : wordResult = wordOutput := by
                            simpa [hwordHandler] using hword'.symm
                          subst loopResult
                          subst wordResult
                          exact handler_agrees function configurationValue
                            configurationLengthValue arrayValue arrayLengthValue
                            loopState wordState loopOutput wordOutput hlocals
                            hloopHandler hwordHandler

/-!
The same boundary stated against the combined evaluators is the interface
used once a function body may contain both ordinary calls and foreign calls.
For the one-step FFI constructor the call tables are intentionally
irrelevant, but keeping them in the theorem makes the result compose with
the call-aware induction without changing the state relation.
-/
theorem loopToWord_ffi_single_combined_simulation [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (handler_agrees : ∀ function configuration configurationLength array arrayLength
      loopInput wordInput loopOutput wordOutput,
      loopLocalsMappedToRiscV context loopInput.locals wordInput →
      loopHandler function configuration configurationLength array arrayLength loopInput =
        some loopOutput →
      wordHandler function configuration configurationLength array arrayLength wordInput =
        some wordOutput →
      loopLocalsMappedToRiscV context loopOutput.locals wordOutput)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (live : List Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithCallsAndFfi functions loopHandler 1 loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFunctionWithHandlersAndFfi [] wordHandler 1 wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopProgWithCallsAndFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none => simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none => simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength, harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none =>
                  simp [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength,
                    harray, harrayLength] at hloop
              | some arrayLengthValue =>
                  rcases hlocals configuration configurationValue hconfig with
                    ⟨configurationRegister, hconfigurationRegister,
                      hconfigurationValue⟩
                  rcases hlocals configurationLength configurationLengthValue hconfigLength with
                    ⟨configurationLengthRegister, hconfigurationLengthRegister,
                      hconfigurationLengthValue⟩
                  rcases hlocals array arrayValue harray with
                    ⟨arrayRegister, harrayRegister, harrayValue⟩
                  rcases hlocals arrayLength arrayLengthValue harrayLength with
                    ⟨arrayLengthRegister, harrayLengthRegister,
                      harrayLengthValue⟩
                  have hloop' :
                      (loopHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue loopState).bind
                        (fun state => some (LoopResult.normal state)) =
                        some (LoopResult.normal loopResult) := by
                    simpa [evalLoopProgWithCallsAndFfi, hconfig, hconfigLength,
                      harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state => some (WordControlResult.normal state)) =
                        some (WordControlResult.normal wordResult) := by
                    simpa [loopToWordProg,
                      evalWordFunctionWithHandlersAndFfi,
                      hconfigurationRegister, hconfigurationLengthRegister,
                      harrayRegister, harrayLengthRegister,
                      hconfigurationValue, hconfigurationLengthValue,
                      harrayValue, harrayLengthValue] using hword
                  cases hloopHandler : loopHandler function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue loopState with
                  | none => simp [hloopHandler] at hloop'
                  | some loopOutput =>
                      cases hwordHandler : wordHandler function configurationValue
                          configurationLengthValue arrayValue arrayLengthValue wordState with
                      | none => simp [hwordHandler] at hword'
                      | some wordOutput =>
                          have hloopOutput : loopResult = loopOutput := by
                            simpa [hloopHandler] using hloop'.symm
                          have hwordOutput : wordResult = wordOutput := by
                            simpa [hwordHandler] using hword'.symm
                          subst loopResult
                          subst wordResult
                          exact handler_agrees function configurationValue
                            configurationLengthValue arrayValue arrayLengthValue
                            loopState wordState loopOutput wordOutput hlocals
                            hloopHandler hwordHandler

end Flapjack.RiscV
