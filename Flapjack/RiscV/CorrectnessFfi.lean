import Flapjack.Correctness
import Flapjack.RiscV.CakeSoundness
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Ffi
import Flapjack.RiscV.CorrectnessFfiMachine
import Flapjack.RiscV.LocValue

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

/-!
The FFI constructor itself does not consume the available fuel.  Expose that
fact at the simulation boundary so callers composing an FFI action with a
larger call-aware computation can choose any positive fuel budget.
-/
theorem loopToWord_ffi_single_combined_simulation_fuel [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
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
    (fuel : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithCallsAndFfi functions loopHandler (fuel + 1) loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler (fuel + 1) wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  apply loopToWord_ffi_single_combined_simulation context functions loopState wordState
    loopHandler wordHandler handler_agrees function configuration configurationLength array
    arrayLength live hlocals
  · simpa [evalLoopProgWithCallsAndFfi] using hloop
  · simpa [loopToWordProg, evalWordFunctionWithHandlersAndFfi] using hword

/-!
Compose two normal-returning programs under the call/FFI evaluators.  This is
the sequencing rule needed to resume a caller after an external action.  The
component hypotheses are intentionally explicit: later pass-specific proofs
can supply them for calls, FFI, loops, or ordinary instructions without this
generic rule depending on a particular backend lowering.
-/
theorem loopToWord_seq_combined_simulation [NeZero width]
    (context : WordContext)
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (finalLoop : LoopState (Word width))
    (finalWord : State width)
    (hfirst : ∀ middleLoop middleWord,
      evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first =
        some (.normal middleLoop) →
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel wordState
        (loopToWordProg context first) = some (.normal middleWord) →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond : ∀ middleLoop middleWord,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      ∀ finalLoop finalWord,
        evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
          some (.normal finalLoop) →
        evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel middleWord
          (loopToWordProg context second) = some (.normal finalWord) →
        loopLocalsMappedToRiscV context finalLoop.locals finalWord)
    (hloop :
      evalLoopProgWithCallsAndFfi functions loopHandler (fuel + 1) loopState
        (.seq first second) = some (.normal finalLoop))
    (hword :
      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler (fuel + 1) wordState
        (loopToWordProg context (.seq first second)) = some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases hfirstLoop : evalLoopProgWithCallsAndFfi functions loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProgWithCallsAndFfi functions loopHandler fuel middleLoop second =
                some (.normal finalLoop) := by
            simpa [evalLoopProgWithCallsAndFfi, hfirstLoop] using hloop
          cases hfirstWord :
              evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel wordState
                (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondWord :
                      evalWordFunctionWithHandlersAndFfi wordFunctions wordHandler fuel
                        middleWord (loopToWordProg context second) =
                        some (.normal finalWord) := by
                    simpa [loopToWordProg, evalWordFunctionWithHandlersAndFfi,
                      hfirstWord] using hword
                  exact hsecond middleLoop middleWord
                    (hfirst middleLoop middleWord hfirstLoop hfirstWord)
                    finalLoop finalWord hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
              | raised middleWord exception =>
                  simp [loopToWordProg, evalWordFunctionWithHandlersAndFfi, hfirstWord] at hword
      | returned middleLoop values =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | broke middleLoop label =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | continued middleLoop label =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProgWithCallsAndFfi, hfirstLoop] at hloop

/-!
The loop-aware Word evaluator uses a distinct control-result carrier so that
an FFI action in a loop body can be followed by `break`/`continue` or can be
interrupted by a return or raise.  The one-step FFI rule preserves the same
mapped-local relation when reached through the fully composed Loop evaluator.
-/
theorem loopToWord_ffi_loop_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
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
    (fuel : Nat)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState) :
    ∀ loopResult wordResult,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState
          (.ffi function configuration configurationLength array arrayLength live) =
        some (.normal loopResult) →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState
          (loopToWordProg context
            (.ffi function configuration configurationLength array arrayLength live)) =
        some (.normal wordResult) →
      loopLocalsMappedToRiscV context loopResult.locals wordResult := by
  intro loopResult wordResult hloop hword
  cases hconfig : loopState.locals configuration with
  | none => simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig] at hloop
  | some configurationValue =>
      cases hconfigLength : loopState.locals configurationLength with
      | none =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig, hconfigLength] at hloop
      | some configurationLengthValue =>
          cases harray : loopState.locals array with
          | none =>
              simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig, hconfigLength,
                harray] at hloop
          | some arrayValue =>
              cases harrayLength : loopState.locals arrayLength with
              | none =>
                  simp [evalLoopProgWithPrimitiveCallsAndFfi, hconfig,
                    hconfigLength, harray, harrayLength] at hloop
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
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hconfig,
                      hconfigLength, harray, harrayLength] using hloop
                  have hword' :
                      (wordHandler function configurationValue
                        configurationLengthValue arrayValue arrayLengthValue wordState).bind
                        (fun state =>
                          some (RiscV.WordLoopControlResult.normal state)) =
                        some (RiscV.WordLoopControlResult.normal wordResult) := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi,
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
Normal completion composes through a sequence in the loop-aware evaluator.
This is the control-flow rule used to resume a loop body after an FFI action;
the hypotheses remain abstract so the same rule can later be instantiated for
calls and primitive instructions.
-/
theorem loopToWord_seq_loop_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (finalLoop : LoopState (Word width))
    (finalWord : State width)
    (hfirst : ∀ middleLoop middleWord,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          loopState first = some (.normal middleLoop) →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          wordState (loopToWordProg context first) = some (.normal middleWord) →
      loopLocalsMappedToRiscV context middleLoop.locals middleWord)
    (hsecond : ∀ middleLoop middleWord,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      ∀ finalLoop finalWord,
        evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
            middleLoop second = some (.normal finalLoop) →
        RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            middleWord (loopToWordProg context second) = some (.normal finalWord) →
        loopLocalsMappedToRiscV context finalLoop.locals finalWord)
    (hloop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState (.seq first second) = some (.normal finalLoop))
    (hword :
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState (loopToWordProg context (.seq first second)) =
        some (.normal finalWord)) :
    loopLocalsMappedToRiscV context finalLoop.locals finalWord := by
  cases hfirstLoop : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases firstResult with
      | normal middleLoop =>
          have hsecondLoop :
              evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
                  middleLoop second = some (.normal finalLoop) := by
            simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
          cases hfirstWord :
              RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                wordState (loopToWordProg context first) with
          | none =>
              simp [loopToWordProg,
                RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
          | some firstWordResult =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondWord :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                        middleWord (loopToWordProg context second) =
                        some (.normal finalWord) := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  exact hsecond middleLoop middleWord
                    (hfirst middleLoop middleWord hfirstLoop hfirstWord)
                    finalLoop finalWord hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | raised middleWord exception =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | broke middleWord label =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
              | continued middleWord label =>
                  simp [loopToWordProg,
                    RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
      | returned middleLoop values =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | raised middleLoop exception =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | broke middleLoop label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
      | continued middleLoop label =>
          simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop

/-!
The loop-aware evaluator carries all five control outcomes.  This relation
extends the ordinary mapped-local observation with return values,
exceptions, and loop labels so that a sequence can be simulated even when
its first component does not complete normally.
-/
def loopResultMappedToWordLoop [NeZero width] (context : WordContext) :
    LoopResult (Word width) → RiscV.WordLoopControlResult width → Prop
  | .normal loopState, .normal wordState =>
      loopLocalsMappedToRiscV context loopState.locals wordState
  | .returned loopState loopValues, .returned wordState wordValues =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordValues = loopValues
  | .raised loopState loopException, .raised wordState wordException =>
      loopLocalsMappedToRiscV context loopState.locals wordState ∧
        wordException = loopException
  | .broke loopState loopLabel, .broke wordState wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals wordState
  | .continued loopState loopLabel, .continued wordState wordLabel =>
      loopLabel = wordLabel ∧
        loopLocalsMappedToRiscV context loopState.locals wordState
  | _, _ => False

/-!
Sequence composition for the complete loop evaluator.  The first component
may terminate normally, in which case the second component is simulated from
the related intermediate states, or it may propagate any other loop control
result unchanged.
-/
theorem loopToWord_seq_loop_control_simulation [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (fuel : Nat)
    (first second : LoopProg (Word width))
    (loopResult : LoopResult (Word width))
    (wordResult : RiscV.WordLoopControlResult width)
    (hfirst : ∀ firstResult firstWordResult,
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          loopState first = some firstResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          wordState (loopToWordProg context first) = some firstWordResult →
      loopResultMappedToWordLoop context firstResult firstWordResult)
    (hsecond : ∀ middleLoop middleWord secondResult secondWordResult,
      loopLocalsMappedToRiscV context middleLoop.locals middleWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          middleLoop second = some secondResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          middleWord (loopToWordProg context second) = some secondWordResult →
      loopResultMappedToWordLoop context secondResult secondWordResult)
    (hloop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler (fuel + 1)
          loopState (.seq first second) = some loopResult)
    (hword :
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler (fuel + 1)
          wordState (loopToWordProg context (.seq first second)) = some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  cases hfirstLoop : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      loopHandler fuel loopState first with
  | none =>
      simp [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] at hloop
  | some firstResult =>
      cases hfirstWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            wordState (loopToWordProg context first) with
      | none =>
          simp [loopToWordProg,
            RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] at hword
      | some firstWordResult =>
          have hfirstResult := hfirst firstResult firstWordResult hfirstLoop hfirstWord
          cases firstResult with
          | normal middleLoop =>
              cases firstWordResult with
              | normal middleWord =>
                  have hsecondLoop :
                      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
                          middleLoop second = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hsecondWord :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
                          middleWord (loopToWordProg context second) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  exact hsecond middleLoop middleWord loopResult wordResult
                    hfirstResult hsecondLoop hsecondWord
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | returned middleLoop values =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord wordValues =>
                  have hloop' :
                      some (.returned middleLoop values) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.returned middleWord wordValues) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | raised middleLoop exception =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord wordException =>
                  have hloop' :
                      some (.raised middleLoop exception) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.raised middleWord wordException) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | broke middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord label =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | broke middleLoop label =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord wordLabel =>
                  have hloop' :
                      some (.broke middleLoop label) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.broke middleWord wordLabel) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult
              | continued middleWord wordLabel =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
          | continued middleLoop label =>
              cases firstWordResult with
              | normal middleWord =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | returned middleWord values =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | raised middleWord exception =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | broke middleWord wordLabel =>
                  simp [loopResultMappedToWordLoop] at hfirstResult
              | continued middleWord wordLabel =>
                  have hloop' :
                      some (.continued middleLoop label) = some loopResult := by
                    simpa [evalLoopProgWithPrimitiveCallsAndFfi, hfirstLoop] using hloop
                  have hword' :
                      some (.continued middleWord wordLabel) = some wordResult := by
                    simpa [loopToWordProg,
                      RiscV.evalWordLoopProgWithHandlersAndFfi, hfirstWord] using hword
                  injection hloop' with hloopResult
                  injection hword' with hwordResult
                  subst loopResult
                  subst wordResult
                  exact hfirstResult

/-
/-!
Handler-free single-parameter calls at a loop boundary.  The callee may
itself use the fully composed primitive/call/FFI evaluator; the abstract
body hypothesis supplies the corresponding five-way Loop/Word relation.
The call dispatcher then proves the caller-frame transition and propagates
all control outcomes.
-/
theorem loopToWord_call_loop_control_simulation_single_parameter [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (target parameter argument : Nat) (argumentValue : Word width)
    (fuel : Nat) (loopBody : LoopProg (Word width))
    (parameterRegister : Fin 32)
    (loopResult : LoopResult (Word width))
    (wordResult : WordLoopControlResult width)
    (hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hbody : ∀ calleeLoop calleeWord bodyResult bodyWordResult,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          calleeLoop loopBody = some bodyResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          calleeWord (loopToWordProg context loopBody) = some bodyWordResult →
      loopResultMappedToWordLoop context bodyResult bodyWordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithPrimitiveCallsAndFfi primitive functions loopHandler
        (fuel + 1) loopState none (some target) [argument] none =
        some loopResult)
    (hword :
      RiscV.evalWordLoopCallWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState none (some target)
        [wordFindVar context argument] none = some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  rcases hlocals argument argumentValue hargument with
    ⟨argumentRegister, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, hcallee⟩
  cases hbodyLoop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop, hreadLoop,
        hcalleeBind, hbodyLoop] at hloop
  | some bodyResult =>
      cases hbodyWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            calleeWord (loopToWordProg context loopBody) with
      | none =>
          simp [RiscV.evalWordLoopCallWithHandlersAndFfi, hlookupWord,
            harguments, hwordBind, hbodyWord] at hword
      | some bodyWordResult =>
          have hbodyResult := hbody { loopState with locals := calleeLocals } calleeWord
            bodyResult bodyWordResult hcallee hbodyLoop hbodyWord
          have callerMapped : ∀ (bodyWordState : State width),
              loopLocalsMappedToRiscV context loopState.locals bodyWordState →
              loopLocalsMappedToRiscV context loopState.locals bodyWordState :=
            fun _ h => h
          cases bodyResult with
          | normal bodyLoopState =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hloop' :
                      some (.normal
                        { bodyLoopState with locals := loopState.locals }) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.normal returnedWordState) = some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact callerMapped returnedWordState hlocals
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | returned bodyLoopState values =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState wordValues =>
                  have hloop' :
                      some (.returned
                        { bodyLoopState with locals := loopState.locals } values) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.returned returnedWordState wordValues) =
                        some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | raised bodyLoopState exception =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState wordException =>
                  have hloop' :
                      some (.raised
                        { bodyLoopState with locals := loopState.locals } exception) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.raised returnedWordState wordException) =
                        some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | broke bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  have hloop' :
                      some (.broke
                        { bodyLoopState with locals := loopState.locals } label) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.broke returnedWordState wordLabel) = some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
              | continued bodyWordState wordLabel =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | continued bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exception =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState wordLabel =>
                  have hloop' :
                      some (.continued
                        { bodyLoopState with locals := loopState.locals } label) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.continued returnedWordState wordLabel) =
                        some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩

/-!
The same call boundary with an exception handler.  The callee still has the
full five-way control relation, while a raised callee result is resumed by
the source and Word handler bodies from related caller states.
-/
theorem loopToWord_call_loop_control_simulation_single_parameter_with_handler
    [NeZero width]
    (context : WordContext)
    (primitive : LoopPrimitiveHandler (Word width))
    (functions : List (Nat × List Nat × LoopProg (Word width)))
    (wordFunctions : List (Nat × List Nat × WordProg (Word width)))
    (loopState : LoopState (Word width))
    (wordState : State width)
    (loopHandler : FunName → Word width → Word width → Word width → Word width →
      LoopState (Word width) → Option (LoopState (Word width)))
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (target parameter argument exception : Nat) (argumentValue : Word width)
    (fuel : Nat) (loopBody handlerBody : LoopProg (Word width))
    (parameterRegister exceptionRegister : Fin 32)
    (loopResult : LoopResult (Word width))
    (wordResult : WordLoopControlResult width)
    (_hlookupLoop :
      lookupLoopFunction target functions = some ([parameter], loopBody))
    (_hlookupWord :
      RiscV.lookupWordFunction target wordFunctions =
        some ([wordFindVar context parameter], loopToWordProg context loopBody))
    (hparameter :
      RiscV.registerOfNat (wordFindVar context parameter) =
        some parameterRegister)
    (hparameter_nonzero : parameterRegister ≠ 0)
    (hexception :
      RiscV.registerOfNat (wordFindVar context exception) =
        some exceptionRegister)
    (hexception_nonzero : exceptionRegister ≠ 0)
    (hargument : loopState.locals argument = some argumentValue)
    (hnoalias :
      ∀ name, name ≠ exception →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
            register ≠ exceptionRegister)
    (hbody : ∀ calleeLoop calleeWord bodyResult bodyWordResult,
      loopLocalsMappedToRiscV context calleeLoop.locals calleeWord →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          calleeLoop loopBody = some bodyResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          calleeWord (loopToWordProg context loopBody) = some bodyWordResult →
      loopResultMappedToWordLoop context bodyResult bodyWordResult)
    (hhandler : ∀ exceptionValue
        (handlerLoopState : LoopState (Word width))
        (handlerWordState : State width)
        (handlerResult : LoopResult (Word width))
        (handlerWordResult : WordLoopControlResult width),
      handlerLoopState.locals =
        updateLoopLocal loopState.locals exception exceptionValue →
      loopLocalsMappedToRiscV context
          (updateLoopLocal loopState.locals exception exceptionValue)
          handlerWordState →
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
          handlerLoopState
          handlerBody = some handlerResult →
      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
          handlerWordState (loopToWordProg context handlerBody) =
            some handlerWordResult →
      loopResultMappedToWordLoop context handlerResult handlerWordResult)
    (hlocals : loopLocalsMappedToRiscV context loopState.locals wordState)
    (hloop :
      evalLoopCallWithPrimitiveCallsAndFfi primitive functions loopHandler
        (fuel + 1) loopState none (some target) [argument]
        (some (exception, handlerBody, .skip, [])) = some loopResult)
    (hword :
      RiscV.evalWordLoopCallWithHandlersAndFfi wordFunctions wordHandler
        (fuel + 1) wordState none (some target)
        [wordFindVar context argument]
        (some (wordFindVar context exception, loopToWordProg context handlerBody,
          0, 0)) =
          some wordResult) :
    loopResultMappedToWordLoop context loopResult wordResult := by
  rcases hlocals argument argumentValue hargument with
    ⟨argumentRegister, hargumentRegister, hargumentValue⟩
  have hreadLoop :
      loopReadLocals loopState.locals [argument] = some [argumentValue] := by
    simp [loopReadLocals, hargument]
  have harguments :
      RiscV.readWordRegisters wordState [wordFindVar context argument] =
        some [argumentValue] := by
    simp [RiscV.readWordRegisters, hargumentRegister, hargumentValue]
  rcases loopBindParameters_single_parameter_agreement context wordState
      parameter argumentValue parameterRegister hparameter hparameter_nonzero with
    ⟨calleeLocals, calleeWord, hcalleeBind, hwordBind, hcallee⟩
  cases hbodyLoop :
      evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopHandler fuel
        { loopState with locals := calleeLocals } loopBody with
  | none =>
      simp [evalLoopCallWithPrimitiveCallsAndFfi, hbodyLoop] at hloop
  | some bodyResult =>
      cases hbodyWord :
          RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions wordHandler fuel
            calleeWord (loopToWordProg context loopBody) with
      | none =>
          simp [RiscV.evalWordLoopCallWithHandlersAndFfi, hbodyWord] at hword
      | some bodyWordResult =>
          have hbodyResult := hbody { loopState with locals := calleeLocals }
            calleeWord bodyResult bodyWordResult hcallee hbodyLoop hbodyWord
          have callerMapped : ∀ (bodyWordState : State width),
              loopLocalsMappedToRiscV context loopState.locals bodyWordState →
              loopLocalsMappedToRiscV context loopState.locals bodyWordState :=
            fun _ h => h
          cases bodyResult with
          | normal bodyLoopState =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  have hloop' :
                      some (.normal
                        { bodyLoopState with locals := loopState.locals }) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.normal returnedWordState) = some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact callerMapped returnedWordState hlocals
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | returned bodyLoopState values =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState wordValues =>
                  have hloop' :
                      some (.returned
                        { bodyLoopState with locals := loopState.locals } values) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.returned returnedWordState wordValues) =
                        some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨callerMapped returnedWordState hlocals,
                    hbodyResult.2⟩
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | broke bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState wordLabel =>
                  have hloop' :
                      some (.broke
                        { bodyLoopState with locals := loopState.locals } label) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.broke returnedWordState wordLabel) = some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
          | continued bodyLoopState label =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState exceptionValue =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState wordLabel =>
                  have hloop' :
                      some (.continued
                        { bodyLoopState with locals := loopState.locals } label) =
                        some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hword' :
                      some (.continued returnedWordState wordLabel) =
                        some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi,
                      hlookupWord, harguments, hwordBind, hbodyWord] at hword
                  cases hloop'
                  cases hword'
                  exact ⟨hbodyResult.1, callerMapped returnedWordState hlocals⟩
          | raised bodyLoopState sourceException =>
              cases bodyWordResult with
              | normal bodyWordState =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | returned bodyWordState values =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | raised bodyWordState targetException =>
                  have hloopHandler :
                      evalLoopProgWithPrimitiveCallsAndFfi primitive functions
                        loopHandler fuel
                        { bodyLoopState with
                          locals := updateLoopLocal loopState.locals exception
                            sourceException }
                        handlerBody = some loopResult := by
                    simp [evalLoopCallWithPrimitiveCallsAndFfi, hlookupLoop,
                      hreadLoop, hcalleeBind, hbodyLoop] at hloop
                  let returnedWordState : State width :=
                    { wordState with
                      memory := bodyWordState.memory
                      privilege := bodyWordState.privilege
                      mode := bodyWordState.mode }
                  have hexceptionValue : sourceException = targetException :=
                    hbodyResult.2.symm
                  have hwordHandler :
                      RiscV.evalWordLoopProgWithHandlersAndFfi wordFunctions
                        wordHandler fuel
                        (RiscV.writeRegister returnedWordState exceptionRegister
                          sourceException)
                        (loopToWordProg context handlerBody) = some wordResult := by
                    simp [RiscV.evalWordLoopCallWithHandlersAndFfi, hlookupWord,
                      harguments, hwordBind, hbodyWord, hexception,
                      hexceptionValue] at hword
                  have hreturnedLocals :
                      loopLocalsMappedToRiscV context loopState.locals
                        returnedWordState := by
                    intro name value hvalue
                    rcases hlocals name value hvalue with
                      ⟨register, hregister, hregisterValue⟩
                    exact ⟨register, hregister, hregisterValue⟩
                  have hhandlerLocals :=
                    loopLocalsMappedToRiscV_update context loopState.locals
                      returnedWordState exception exceptionRegister sourceException
                      hreturnedLocals hexception hexception_nonzero hnoalias
                  exact hhandler sourceException
                    { bodyLoopState with
                      locals := updateLoopLocal loopState.locals exception
                        sourceException }
                    (RiscV.writeRegister returnedWordState exceptionRegister
                      sourceException)
                    loopResult wordResult rfl hhandlerLocals hloopHandler hwordHandler
              | broke bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult
              | continued bodyWordState label =>
                  simp [loopResultMappedToWordLoop] at hbodyResult

-/

/-! The FFI-aware selector delegates ordinary straight-line instructions to
    the call-aware selector unchanged.  This keeps the host-effect boundary
    isolated from the deterministic instruction-selection contract. -/

theorem wordFunctionToRiscVWithCallsAndFfi_agrees_straightLine [NeZero width]
    (context : WordCallFfiContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    wordFunctionToRiscVWithCallsAndFfi context program =
      wordFunctionToRiscVWithCalls
        { targets := context.targets } program := by
  induction hstraight with
  | skip =>
      simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls]
  | move store moves =>
      cases h : wordMoveToInstructions (width := width) moves <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls, h]
  | assign destination value =>
      cases h : wordExpToInstructions (width := width) destination value <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls, h]
  | inst instruction =>
      cases h : wordFunctionToRiscVWithCalls { targets := context.targets }
          (.inst instruction) <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, h]
  | store address value =>
      cases h : wordStoreToInstructions (width := width) address value <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls, h]
  | locValue destination source =>
      cases h : wordLocValueToInstructions (width := width) destination source <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls,
          h]
  | tick =>
      simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls]
  | shareInst operator name address =>
      cases h : wordShareInstToInstructions (width := width) operator name address <;>
        simp [wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp [wordFunctionToRiscVWithCallsAndFfi,
        wordFunctionToRiscVWithCalls, ihfirst, ihsecond]

/-! The call-aware Cake-faithful selector lowers `Loc` values to the exact
    original CakeML `riscv_ast (Loc r i)` shape: an `AUIPC`/`ADDI` pair whose
    offset is `label - position`.  The lemmas below expose that shape and the
    register-level readback needed by the FFI boundary, with the source program
    counter made explicit. -/

theorem wordFunctionToRiscVWithCallsCake_locValue [NeZero width]
    (context : WordCallContext width) (destination source : Nat) :
    wordFunctionToRiscVWithCallsCake context
        ((.locValue destination source) : WordProg (Word width)) =
      (wordLocValueToInstructionsCake (width := width) destination source 0).map
        (fun instructions => (instructions, [])) := by
  cases h : wordLocValueToInstructionsCake (width := width) destination source 0 <;>
    simp [wordFunctionToRiscVWithCallsCake, h]

theorem wordFunctionToRiscVWithCallsCake_locValue_execution
    (_context : WordCallContext 64) (state : State 64)
    (destination source : Nat) (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hpc : state.pc = BitVec.ofNat 64 0)
    (hsource : (source : Int) < 2 ^ 19) :
    readRegister
      (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) destination source 0).getD []))
      ⟨destination, hdestination⟩ = BitVec.ofNat 64 source := by
  exact wordLocValueToInstructionsCake_execution_general state destination source 0
    hdestination hdestinationNonzero hpc (by omega) (by simpa using hsource)

/-- Regression: the call-aware Cake selector compiles `Loc 4 0x1234` to the
    `AUIPC`/`ADDI` pair with no leading fallback entry. -/
example (context : WordCallContext 64) :
    wordFunctionToRiscVWithCallsCake context
        ((.locValue 4 0x1234) : WordProg (Word 64)) =
      some ([.auipc 4 (BitVec.ofInt 64 1), .addi 4 4 (BitVec.ofInt 64 0x234)], []) := by
  simp [wordFunctionToRiscVWithCallsCake, wordLocValueToInstructionsCake, registerOfNat]

/-! The Cake-faithful FFI-aware selector is definitionally the Cake call-aware
    selector on straight-line programs, so the exact `AUIPC`/`ADDI` `Loc`
    lowering and its register readback are inherited by the FFI boundary. -/

theorem wordFunctionToRiscVWithCallsAndFfiCake_agrees_straightLine [NeZero width]
    (context : WordCallFfiContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program) :
    wordFunctionToRiscVWithCallsAndFfiCake context program =
      wordFunctionToRiscVWithCallsCake
        { targets := context.targets } program := by
  induction hstraight with
  | skip =>
      simp [wordFunctionToRiscVWithCallsAndFfiCake, wordFunctionToRiscVWithCallsCake]
  | move store moves =>
      cases h : wordMoveToInstructions (width := width) moves <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake,
          wordFunctionToRiscVWithCallsCake, h]
  | assign destination value =>
      cases h : wordExpToInstructionsCake (width := width) destination value <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake,
          wordFunctionToRiscVWithCallsCake, h]
  | inst instruction =>
      cases h : wordFunctionToRiscVWithCallsCake { targets := context.targets }
          (.inst instruction) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake, h]
  | store address value =>
      cases h : wordShareInstToInstructionsCake .store value address <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake,
          wordFunctionToRiscVWithCallsCake, h]
  | locValue destination source =>
      cases h : wordLocValueToInstructionsCake (width := width) destination source 0 <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake,
          wordFunctionToRiscVWithCallsCake, h]
  | tick =>
      simp [wordFunctionToRiscVWithCallsAndFfiCake, wordFunctionToRiscVWithCallsCake]
  | shareInst operator name address =>
      cases h : wordShareInstToInstructionsCake operator name address <;>
        simp [wordFunctionToRiscVWithCallsAndFfiCake,
          wordFunctionToRiscVWithCallsCake, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp [wordFunctionToRiscVWithCallsAndFfiCake,
        wordFunctionToRiscVWithCallsCake, ihfirst, ihsecond]

/-! The FFI-aware Cake selector has the same evaluator soundness on the
    straight-line fragment as its call-aware sibling.  The straight-line
    premise excludes foreign effects, so the existing Cake evaluator relation
    is the exact state contract needed here. -/
theorem wordFunctionToRiscVWithCallsAndFfiCake_sound_of_straightLine
    [NeZero width] (context : WordCallFfiContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCallsAndFfiCake context program =
      some (code, [])) :
    evalWordFunctionCake state program =
      some (executeInstructions state code, []) := by
  have hagree := wordFunctionToRiscVWithCallsAndFfiCake_agrees_straightLine
    context program hstraight
  rw [hagree] at hcompile
  exact wordFunctionToRiscVWithCallsCake_sound_of_straightLine
    { targets := context.targets } state program hstraight code hcompile

theorem wordFunctionToRiscVWithCallsAndFfiCake_locValue [NeZero width]
    (context : WordCallFfiContext width) (destination source : Nat) :
    wordFunctionToRiscVWithCallsAndFfiCake context
        ((.locValue destination source) : WordProg (Word width)) =
      (wordLocValueToInstructionsCake (width := width) destination source 0).map
        (fun instructions => (instructions, [])) := by
  cases h : wordLocValueToInstructionsCake (width := width) destination source 0 <;>
    simp [wordFunctionToRiscVWithCallsAndFfiCake,
      wordFunctionToRiscVWithCallsCake, h]

theorem wordFunctionToRiscVWithCallsAndFfiCake_locValue_execution
    (_context : WordCallFfiContext 64) (state : State 64)
    (destination source : Nat) (hdestination : destination < 32)
    (hdestinationNonzero : destination ≠ 0)
    (hpc : state.pc = BitVec.ofNat 64 0)
    (hsource : (source : Int) < 2 ^ 19) :
    readRegister
      (executeInstructions state
        ((wordLocValueToInstructionsCake (width := 64) destination source 0).getD []))
      ⟨destination, hdestination⟩ = BitVec.ofNat 64 source := by
  exact wordLocValueToInstructionsCake_execution_general state destination source 0
    hdestination hdestinationNonzero hpc (by omega) (by simpa using hsource)

/-! The FFI-aware Cake boundary preserves complete constant materialization for
    ordinary assignments, just as the non-FFI Cake selector does.  The
    return-carrier composition is covered by the exact regression in
    `RiscVConstantParity`. -/
theorem wordFunctionToRiscVWithCallsAndFfiCake_const_assign
    [NeZero width] (context : WordCallFfiContext width) (destination : Nat)
    (value : Word width) :
    wordFunctionToRiscVWithCallsAndFfiCake context
        (.assign destination (.const value)) =
      (wordConstToInstructions destination value).map
        (fun instructions => (instructions, [])) := by
  cases h : wordConstToInstructions destination value <;>
    simp [wordFunctionToRiscVWithCallsAndFfiCake,
      wordFunctionToRiscVWithCallsCake, wordExpToInstructionsCake,
      Option.map, Option.bind, h]

/-- Regression: the FFI-aware Cake selector also lowers `Loc 4 0x1234` to the
    `AUIPC`/`ADDI` pair with no leading fallback entry. -/
example (context : WordCallFfiContext 64) :
    wordFunctionToRiscVWithCallsAndFfiCake context
        ((.locValue 4 0x1234) : WordProg (Word 64)) =
      some ([.auipc 4 (BitVec.ofInt 64 1), .addi 4 4 (BitVec.ofInt 64 0x234)], []) := by
  simp [wordFunctionToRiscVWithCallsAndFfiCake, wordFunctionToRiscVWithCallsCake,
    wordLocValueToInstructionsCake, registerOfNat]

/-! Compose the FFI-aware selector with the ABI return boundary for a
    deterministic straight-line body.  Foreign calls may occur in the
    surrounding function, but this theorem isolates the ordinary body/return
    fragment needed by allocator and function-entry proofs. -/

theorem wordFunctionToRiscVWithCallsAndFfi_seq_return_sound [NeZero width]
    (context : WordCallFfiContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (store : Nat) (values : List Nat)
    (firstCode : List (Instruction width)) (returns : List (Fin 32))
    (hfirstCompile : wordFunctionToRiscVWithCallsAndFfi context program =
      some (firstCode, []))
    (hreturnCompile : wordFunctionToRiscVWithCallsAndFfi context
      ((.return store values) : WordProg (Word width)) =
      some ([], returns)) :
    wordFunctionToRiscVWithCallsAndFfi context
        (.seq program (.return store values)) =
      some (firstCode, returns) ∧
    evalWordFunction state (.seq program (.return store values)) =
      Option.map (fun returned =>
        (executeInstructions state firstCode, returned))
        (values.mapM (fun name => do
          let register ← registerOfNat name
          pure (readRegister (executeInstructions state firstCode) register))) := by
  have hfirstOrdinary : wordFunctionToRiscVWithCalls
      { targets := context.targets } program = some (firstCode, []) := by
    rw [← wordFunctionToRiscVWithCallsAndFfi_agrees_straightLine
      context program hstraight]
    exact hfirstCompile
  have hreturnOrdinary : wordFunctionToRiscVWithCalls
      { targets := context.targets }
      ((.return store values) : WordProg (Word width)) = some ([], returns) := by
    cases hvalues : values.mapM registerOfNat with
    | none =>
        simp [wordFunctionToRiscVWithCallsAndFfi,
          wordFunctionToRiscVWithCalls, hvalues] at hreturnCompile
    | some registers =>
        simpa [wordFunctionToRiscVWithCallsAndFfi,
          wordFunctionToRiscVWithCalls, hvalues] using hreturnCompile
  have hmachine := wordFunctionToRiscVWithCalls_seq_return_sound
    { targets := context.targets } state program hstraight store values
    firstCode returns hfirstOrdinary hreturnOrdinary
  constructor
  · simp [wordFunctionToRiscVWithCallsAndFfi, hfirstCompile, hreturnCompile]
  · exact hmachine.2

/-! The loop-capable FFI selector has the same ordinary straight-line
    normalization as the non-loop FFI selector, and also admits an ECALL leaf.
    No control-flow marker is present in this fragment. -/

inductive WordRiscVFFIStraightLine : WordProg α → Prop where
  | skip : WordRiscVFFIStraightLine (.skip : WordProg α)
  | move (store : Nat) (moves : List (Nat × Nat)) :
      WordRiscVFFIStraightLine (.move store moves)
  | assign (destination : Nat) (value : WordExp α) :
      WordRiscVFFIStraightLine (.assign destination value)
  | inst (instruction : WordInst α) :
      WordRiscVFFIStraightLine (.inst instruction)
  | store (address : WordExp α) (value : Nat) :
      WordRiscVFFIStraightLine (.store address value)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : List Nat × List Nat) :
      WordRiscVFFIStraightLine
        (.ffi function configuration configurationLength array arrayLength live)
  | seq (first second : WordProg α) :
      WordRiscVFFIStraightLine first → WordRiscVFFIStraightLine second →
      WordRiscVFFIStraightLine (.seq first second)
  | locValue (destination source : Nat) :
      WordRiscVFFIStraightLine (.locValue destination source)
  | tick : WordRiscVFFIStraightLine (.tick : WordProg α)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordExp α) :
      WordRiscVFFIStraightLine (.shareInst operator name address)

theorem wordFunctionToRiscVWithCallsAndFfiAndLoopsAux_agrees_straightLine
    [NeZero width] (context : WordCallFfiContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVFFIStraightLine program) :
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux context program =
      (wordFunctionToRiscVWithCallsAndFfi context program).map
        (fun result => (result.1.map .instruction, result.2)) := by
  induction hstraight with
  | skip =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.skip : WordProg (Word width)) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | move store moves =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context (.move store moves) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | assign destination value =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.assign destination value) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | inst instruction =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context (.inst instruction) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | store address value =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context (.store address value) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | ffi function configuration configurationLength array arrayLength live =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.ffi function configuration configurationLength array arrayLength live) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | locValue destination source =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.locValue destination source) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | tick =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.tick : WordProg (Word width)) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | shareInst operator name address =>
      cases h : wordFunctionToRiscVWithCallsAndFfi context
          (.shareInst operator name address) <;>
        simp [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux, h]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      simp only [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux]
      rw [ihfirst, ihsecond]
      simp only [wordFunctionToRiscVWithCallsAndFfi]
      cases hfirstCode : wordFunctionToRiscVWithCallsAndFfi context first with
      | none => simp
      | some firstResult =>
          cases hsecondCode : wordFunctionToRiscVWithCallsAndFfi context second with
          | none =>
              cases firstResult with
              | mk firstCode firstReturns =>
                  cases firstReturns with
                  | nil => simp
                  | cons firstReturn firstReturns => simp
          | some secondResult =>
              cases firstResult with
              | mk firstCode firstReturns =>
                  cases firstReturns with
                  | nil =>
                      cases secondResult with
                      | mk secondCode secondReturns =>
                          simp
                  | cons firstReturn firstReturns =>
                      simp

theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_agrees_straightLine
    [NeZero width] (context : WordCallFfiContext width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVFFIStraightLine program) :
    wordFunctionToRiscVWithCallsAndFfiAndLoops context program =
      wordFunctionToRiscVWithCallsAndFfi context program := by
  simp only [wordFunctionToRiscVWithCallsAndFfiAndLoops]
  rw [wordFunctionToRiscVWithCallsAndFfiAndLoopsAux_agrees_straightLine
    context program hstraight]
  cases h : wordFunctionToRiscVWithCallsAndFfi context program with
  | none => simp
  | some result =>
      cases result with
      | mk code returns =>
          simp [wordControlInstructions_map_instruction]

theorem wordRiscVFFIStraightLine_of_straightLine {α : Type} {program : WordProg α}
    (hstraight : WordRiscVStraightLine program) :
    WordRiscVFFIStraightLine program := by
  induction hstraight with
  | skip => exact .skip
  | move store moves => exact .move store moves
  | assign destination value => exact .assign destination value
  | inst instruction => exact .inst instruction
  | store address value => exact .store address value
  | seq first second hfirst hsecond ihfirst ihsecond =>
      exact .seq first second ihfirst ihsecond
  | locValue destination source => exact .locValue destination source
  | tick => exact .tick
  | shareInst operator name address => exact .shareInst operator name address

/-- Soundness of the most complete (loop- and FFI-aware) static selector on the
ordinary straight-line fragment: an accepted program evaluates to exactly the
emitted instruction sequence.  The loop- and FFI-capable machinery collapses to
the call-aware selector, whose soundness is already established. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_sound_of_straightLine
    [NeZero width] (context : WordCallFfiContext width) (state : State width)
    (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context program =
      some (code, [])) :
    evalWordFunction state program =
      some (executeInstructions state code, []) := by
  have hloops := wordFunctionToRiscVWithCallsAndFfiAndLoops_agrees_straightLine
    context program (wordRiscVFFIStraightLine_of_straightLine hstraight)
  rw [hloops] at hcompile
  have hffi := wordFunctionToRiscVWithCallsAndFfi_agrees_straightLine
    context program hstraight
  rw [hffi] at hcompile
  exact wordFunctionToRiscVWithCalls_sound_of_straightLine
    { targets := context.targets } state program hstraight code hcompile

/-- Regression: the loop/FFI-aware selector soundness fires on a trivial
straight-line program. -/
example (context : WordCallFfiContext 64) (state : State 64) :
    evalWordFunction state (.skip : WordProg (Word 64)) =
      some (executeInstructions state ([] : List (Instruction 64)), []) := by
  have hcompile : wordFunctionToRiscVWithCallsAndFfiAndLoops context
      (.skip : WordProg (Word 64)) =
      some (([] : List (Instruction 64)), []) := by
    simp [wordFunctionToRiscVWithCallsAndFfiAndLoops,
      wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
      wordFunctionToRiscVWithCallsAndFfi, wordFunctionToRiscVWithCalls,
      wordControlInstructions]
  exact wordFunctionToRiscVWithCallsAndFfiAndLoops_sound_of_straightLine
    context state (.skip : WordProg (Word 64)) .skip _ hcompile

/-! The loop-capable selector preserves the one-step ECALL simulation boundary.
    This is the first named machine-correctness theorem for an FFI operation
    after loop-aware lowering. -/
theorem wordFunctionToRiscVWithCallsAndFfiAndLoops_ffi_simulation
    [NeZero width] (context : WordFfiContext)
    (host : WordFfiHost width)
    (wordHandler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (service : Nat) (configurationRegister configurationLengthRegister
      arrayRegister arrayLengthRegister : Fin 32)
    (hservice : lookupWordFfiService function context.services = some service)
    (hservice_bounded : service < 2 ^ width)
    (hconfiguration : registerOfNat configuration = some configurationRegister)
    (hconfigurationLength : registerOfNat configurationLength =
      some configurationLengthRegister)
    (harray : registerOfNat array = some arrayRegister)
    (harrayLength : registerOfNat arrayLength = some arrayLengthRegister)
    (hzero : readRegister state 0 = 0)
    (hsource : ∀ source : Fin 32, source ∈
      [configurationRegister, configurationLengthRegister, arrayRegister,
        arrayLengthRegister] →
      ∀ destination : Fin 32, destination ∈ [10, 11, 12, 13] →
        source ≠ destination)
    (hhandler : host service
      (readRegister state configurationRegister)
      (readRegister state configurationLengthRegister)
      (readRegister state arrayRegister)
      (readRegister state arrayLengthRegister)
      (executeInstructions state
        [.addi 10 configurationRegister (0#width),
         .addi 11 configurationLengthRegister (0#width),
         .addi 12 arrayRegister (0#width), .addi 13 arrayLengthRegister (0#width),
         .addi 14 0 (BitVec.ofNat width service)]) =
      wordHandler function
        (readRegister state configurationRegister)
        (readRegister state configurationLengthRegister)
        (readRegister state arrayRegister)
        (readRegister state arrayLengthRegister) state) :
    (wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := context.services } : WordCallFfiContext width)
      (.ffi function configuration configurationLength array arrayLength ([], []))).bind
        (fun result =>
          (executeInstructionsWithFfi host state result.1).map
            (fun final => (final, ([] : List (Word width))))) =
      evalWordFunctionWithCallsAndFfi [] wordHandler 1 state
        (.ffi function configuration configurationLength array arrayLength ([], [])) := by
  cases hcode : wordFfiToRiscV (width := width) { services := context.services } function
      configuration configurationLength array arrayLength with
  | none =>
      simpa [wordFunctionToRiscVWithCallsAndFfiAndLoops,
        wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
        wordFunctionToRiscVWithCallsAndFfi, hcode] using
        (wordFunctionToRiscVWithCallsAndFfi_ffi_simulation context host wordHandler
          state function configuration configurationLength array arrayLength service
          configurationRegister configurationLengthRegister arrayRegister
          arrayLengthRegister hservice hservice_bounded hconfiguration
          hconfigurationLength harray harrayLength hzero hsource hhandler)
  | some code =>
      simpa [wordFunctionToRiscVWithCallsAndFfiAndLoops,
        wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
        wordFunctionToRiscVWithCallsAndFfi,
        wordControlInstructions_map_instruction, hcode] using
        (wordFunctionToRiscVWithCallsAndFfi_ffi_simulation context host wordHandler
          state function configuration configurationLength array arrayLength service
          configurationRegister configurationLengthRegister arrayRegister
          arrayLengthRegister hservice hservice_bounded hconfiguration
          hconfigurationLength harray harrayLength hzero hsource hhandler)


/-!
The FFI/call-aware evaluator `evalWordFunctionWithCallsAndFfi` keeps the
source state, memory, privilege, mode, and FFI handler visible in its
arguments.  On the straight-line fragment no call, FFI action, or return can
occur, so it must coincide with the plain evaluator `evalWordFunction`.  The
fuel bound is explicit: a program of `n` nested sequences needs `n + 1` fuel
before the evaluator reaches its straight-line fallback.
-/

theorem option_bind_pair_eta {α β : Type} (x : Option (α × β)) :
    x.bind (fun p => some (p.1, p.2)) = x := by
  cases x <;> rfl

theorem evalWordFunctionWithCallsAndFfi_straightLine_eq_evalWordFunction
    {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width)))
    (handler : FunName → Word width → Word width → Word width → Word width →
      State width → Option (State width))
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (fuel : Nat) (hfuel : sizeOf program + 1 ≤ fuel) :
    evalWordFunctionWithCallsAndFfi functions handler fuel state program =
      evalWordFunction state program := by
  induction hstraight generalizing state fuel with
  | skip => cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | move store moves =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | assign destination value =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | inst instruction =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | store address value =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | locValue destination source =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | tick => cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | shareInst operator name address =>
      cases fuel with | zero => omega | succ k => simp [evalWordFunctionWithCallsAndFfi]
  | seq first second hfirst hsecond ihfirst ihsecond =>
      cases fuel with
      | zero => omega
      | succ k =>
          have hk : sizeOf first + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          have hk2 : sizeOf second + 1 ≤ k := by
            have hs : sizeOf (WordProg.seq first second) =
                1 + sizeOf first + sizeOf second := rfl
            omega
          simp only [evalWordFunctionWithCallsAndFfi, evalWordFunction]
          rw [ihfirst state k hk]
          rw [evalWordFunction_wordRiscVStraightLine_eq_evalWordProg state first hfirst]
          cases heval : evalWordProg state first with
          | none => simp
          | some firstState =>
              simp [ihsecond firstState k hk2, option_bind_pair_eta]

/-- Regression: the FFI/call-aware evaluator agrees with the plain evaluator on
a straight-line skip once the fuel exceeds the program size. -/
example (functions : List (Nat × List Nat × WordProg (Word 64)))
    (handler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
      State 64 → Option (State 64)) (state : State 64) :
    evalWordFunctionWithCallsAndFfi functions handler
        (sizeOf (.skip : WordProg (Word 64)) + 1) state
        (.skip : WordProg (Word 64)) =
      evalWordFunction state (.skip : WordProg (Word 64)) :=
  evalWordFunctionWithCallsAndFfi_straightLine_eq_evalWordFunction functions
    handler state (.skip : WordProg (Word 64)) .skip _ (Nat.le_refl _)

end Flapjack.RiscV
