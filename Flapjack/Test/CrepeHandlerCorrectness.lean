import Flapjack.CrepeFfiCorrectness
import Flapjack.CrepeCallHandlerCorrectness
import Flapjack.RiscV.Model

/-! Concrete caught-call regression for the full-Crepe handler boundary. -/

namespace Flapjack

open RiscV

def crepeHandlerCallContext : CompileContext (Word 64) :=
  { vars := [("exn", (.one, [1]))]
    functions := [("raise", ([], .one))]
    exceptions := [("E", BitVec.ofNat 64 7)]
    maxVar := 1
    bytesInWord := BitVec.ofNat 64 8 }

def crepeHandlerCallSource : Prog (Word 64) :=
  .call (some (none, some ("E", "exn", .return (.var .local "exn"))))
    "raise" []

def crepeHandlerCallFunctions : List (CompiledFunction (Word 64)) :=
  [{ name := "raise", params := [],
     body := .seq (.storeGlob (BitVec.ofNat 64 0) (.const (BitVec.ofNat 64 7)))
       (.raise (BitVec.ofNat 64 7)),
     returnShape := .one }]

def crepeHandlerCallCaller : CrepState (Word 64) :=
  { locals := fun _ => none, memory := fun _ => none }

def crepeHandlerCallReturnedState : CrepState (Word 64) :=
  { locals := updateCrepLocal (fun _ => none) 1 (BitVec.ofNat 64 7)
    memory := updateMemory (fun _ => none) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 7) }

def crepeHandlerCallResult : CrepControlResult (Word 64) :=
  .returned crepeHandlerCallReturnedState [BitVec.ofNat 64 7]

def crepeHandlerCallSourceFunctions :
    List (FunName × List VarName × Prog (Word 64)) :=
  [("raise", [], .raise "E" (.const (BitVec.ofNat 64 7)))]

def crepeHandlerCallContinuation : Prog (Word 64) :=
  .return (.const (BitVec.ofNat 64 99))

def crepeHandlerCallSequence : Prog (Word 64) :=
  .seq crepeHandlerCallSource crepeHandlerCallContinuation

theorem crepe_handler_call_simulation_regression :
    evalCrepFullProg crepeHandlerCallFunctions
        (fun _ _ => none) (noCrepFfi (Word 64))
        defaultCrepSharedMem 0 100 9 crepeHandlerCallCaller
        (compileProg crepeHandlerCallContext crepeHandlerCallSource) =
      some crepeHandlerCallResult := by
  apply compile_full_call_handler_simulation
    (context := crepeHandlerCallContext)
    (functions := crepeHandlerCallFunctions)
    (primitive := fun _ _ => none)
    (ffi := noCrepFfi (Word 64))
    (sharedMem := defaultCrepSharedMem)
    (baseAddress := 0) (topAddress := 100) (fuel := 8)
    (caller := crepeHandlerCallCaller) (function := "raise")
    (arguments := []) (compiledArguments := []) (returnShape := .one)
    (exception := "E") (handlerVar := "exn")
    (exceptionCode := BitVec.ofNat 64 7)
    (handlerProgram := .return (.var .local "exn"))
    (handlerNames := [1]) (result := crepeHandlerCallResult)
  · simp [crepeHandlerCallContext, lookupInfo]
  · simp [crepeHandlerCallContext, lookupInfo]
  · simp [crepeHandlerCallContext, lookupInfo]
  · simp [compileArgs]
  · have hexn : lookupInfo "exn" [("exn", (Shape.one, [1]))] =
        some (Shape.one, [1]) := by
      simp [lookupInfo]
    simp [crepeHandlerCallContext, crepeHandlerCallFunctions,
      crepeHandlerCallCaller,
      crepeHandlerCallResult, crepeHandlerCallReturnedState,
      evalCrepFullCall, evalCrepFullProg,
      evalCrepFullExps, evalCrepFullExp, assignCrepValues, assignRet,
      crepNestedSeq, loadGlobals, compileProg, compileExp,
      updateCrepLocal, updateMemory, lookupCompiledFunction, hexn]

theorem pan_value_caught_handler_equation_regression :
    evalPanValueCallWithPrimitiveCallsAndFfi
        (fun _ _ => none) (fun _ _ _ _ _ _ => none)
        [] crepeHandlerCallSourceFunctions
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 9
        (fun _ => none) (fun _ => none) (fun _ => none)
        (some (none, some ("E", "exn",
          (.return (.var .local "exn"))))) "raise" [] =
      some (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        [.word (BitVec.ofNat 64 7)]) := by
  apply evalPanValueCall_caught_handler_of_eval
    (primitive := fun _ _ => none)
    (handler := fun _ _ _ _ _ _ => none)
    (structs := []) (functions := crepeHandlerCallSourceFunctions)
    (sourceLocals := fun _ => none) (sourceGlobals := fun _ => none)
    (sourceMemory := fun _ => none)
    (baseAddress := BitVec.ofNat 64 0)
    (topAddress := BitVec.ofNat 64 100)
    (bytesInWord := BitVec.ofNat 64 8) (fuel := 8)
    (contracts := none) (memoryAccess := none) (memoryHandler := none)
    (function := "raise") (arguments := []) (values := [])
    (parameters := [])
    (body := .raise "E" (.const (BitVec.ofNat 64 7)))
    (calleeLocals := fun _ => none) (calleeBodyLocals := fun _ => none)
    (calleeGlobals := fun _ => none) (calleeMemory := fun _ => none)
    (sourceException := "E")
    (sourceValue := .word (BitVec.ofNat 64 7))
    (caught := "E") (handlerVariable := "exn")
    (handlerProgram := .return (.var .local "exn"))
    (sourceResult := .returned (fun _ => none) (fun _ => none)
      (fun _ => none) [.word (BitVec.ofNat 64 7)])
  all_goals
    simp [crepeHandlerCallSourceFunctions, evalPanValueExps,
      evalPanValueExp.evalPanValueExps, evalPanValueExp,
      evalPanValueProgWithPrimitiveCallsAndFfi, lookupPanFunction,
      bindPanValueParameters, updatePanValueMap, panValueParametersValid,
      panValueExceptionValid, panValuePayloadWithinLimit,
      panValueHandlerValid]
  all_goals decide

theorem crepe_handler_call_return_short_circuits_regression :
    evalCrepFullProg crepeHandlerCallFunctions
        (fun _ _ => none) (noCrepFfi (Word 64))
        defaultCrepSharedMem 0 100 10 crepeHandlerCallCaller
        (compileProg crepeHandlerCallContext crepeHandlerCallSequence) =
      some crepeHandlerCallResult ∧
    evalPanProgWithCallsAndFfi crepeHandlerCallSourceFunctions
        (fun _ _ _ _ _ _ => none) 10 (fun _ => none)
        crepeHandlerCallSequence =
      some (.returned
        (updatePanLocal (fun _ => none) "exn" (BitVec.ofNat 64 7))
        [BitVec.ofNat 64 7]) := by
  apply compile_full_seq_after_return_simulation
    (context := crepeHandlerCallContext)
    (functions := crepeHandlerCallFunctions)
    (sourceFunctions := crepeHandlerCallSourceFunctions)
    (sourceLocals := fun _ => none)
    (sourceLocals' := updatePanLocal (fun _ => none) "exn"
      (BitVec.ofNat 64 7))
    (state := crepeHandlerCallCaller)
    (state' := crepeHandlerCallReturnedState)
    (primitive := fun _ _ => none)
    (ffi := noCrepFfi (Word 64))
    (sharedMem := defaultCrepSharedMem)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 100) (fuel := 8)
    (first := crepeHandlerCallSource)
    (compiledFirst := compileProg crepeHandlerCallContext crepeHandlerCallSource)
    (second := crepeHandlerCallContinuation)
    (compiledSecond := compileProg crepeHandlerCallContext
      crepeHandlerCallContinuation)
    (sourceValues := [BitVec.ofNat 64 7])
    (crepValues := [BitVec.ofNat 64 7])
    (hfirstCompile := rfl) (hsecondCompile := rfl)
    (hfirstCrep := by
      exact crepe_handler_call_simulation_regression)
    (hfirstSource := by
      simp [crepeHandlerCallSourceFunctions, crepeHandlerCallSource,
        evalPanProgWithCallsAndFfi, evalPanCallWithCallsAndFfi,
        evalPanExps, evalPanExp, lookupPanFunction, bindPanParameters,
        updatePanLocal])

def crepeRaiseContext : CompileContext (Word 64) :=
  { vars := [], functions := [],
    exceptions := [("E", BitVec.ofNat 64 7)],
    maxVar := 0, bytesInWord := BitVec.ofNat 64 8 }

def crepeRaiseState : CrepState (Word 64) :=
  { locals := fun _ => none, memory := fun _ => none }

def crepeRaiseSource : Prog (Word 64) :=
  .raise "E" (.const (BitVec.ofNat 64 7))

theorem crepe_raise_simulation_regression :
    evalCrepFullProg [] (fun _ _ => none) (noCrepFfi (Word 64))
        defaultCrepSharedMem 0 100 10 crepeRaiseState
        (compileProg crepeRaiseContext crepeRaiseSource) =
      some (.raised
        (restoreCrepOneTemp
          { crepeRaiseState with
            memory := updateMemory crepeRaiseState.memory 0
              (BitVec.ofNat 64 7) }
          crepeRaiseState 1)
        (BitVec.ofNat 64 7)) ∧
    evalPanProgWithCallsAndFfi [] (fun _ _ _ _ _ _ => none) 6
        (fun _ => none) crepeRaiseSource =
      some (.raised (fun _ => none) "E" (BitVec.ofNat 64 7)) := by
  apply compile_full_raise_simulation
    (context := crepeRaiseContext)
    (sourceLocals := fun _ => none)
    (state := crepeRaiseState)
    (primitive := fun _ _ => none)
    (ffi := noCrepFfi (Word 64))
    (sharedMem := defaultCrepSharedMem)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 100) (fuel := 5)
    (exception := "E") (exceptionCode := BitVec.ofNat 64 7)
    (value := .const (BitVec.ofNat 64 7))
    (compiledValue := .const (BitVec.ofNat 64 7))
    (sourceValue := BitVec.ofNat 64 7)
    (targetValue := BitVec.ofNat 64 7)
  · simp [crepeRaiseContext, compileExp]
  · simp [crepeRaiseContext, lookupInfo]
  · simp [evalPanExp]
  · simp [crepeRaiseState, evalCrepFullExp]
  · rfl

theorem crepe_return_simulation_regression :
    evalCrepFullProg [] (fun _ _ => none) (noCrepFfi (Word 64))
        defaultCrepSharedMem 0 100 10 crepeRaiseState
        (compileProg crepeRaiseContext
          (.return (.const (BitVec.ofNat 64 9)))) =
      some (.returned crepeRaiseState [BitVec.ofNat 64 9]) ∧
    evalPanProgWithCallsAndFfi [] (fun _ _ _ _ _ _ => none) 10
        (fun _ => none)
        (.return (.const (BitVec.ofNat 64 9))) =
      some (.returned (fun _ => none) [BitVec.ofNat 64 9]) := by
  apply compile_full_return_simulation
    (context := crepeRaiseContext)
    (sourceLocals := fun _ => none)
    (state := crepeRaiseState)
    (primitive := fun _ _ => none)
    (ffi := noCrepFfi (Word 64))
    (sharedMem := defaultCrepSharedMem)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 100) (fuel := 9)
    (value := .const (BitVec.ofNat 64 9))
    (compiledValue := .const (BitVec.ofNat 64 9))
    (sourceValue := BitVec.ofNat 64 9)
    (targetValue := BitVec.ofNat 64 9)
  · simp [crepeRaiseContext, compileExp]
  · simp [evalPanExp]
  · simp [crepeRaiseState, evalCrepFullExp]
  · rfl

end Flapjack
