import Flapjack.CrepeFfiCorrectness
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

def crepeHandlerCallResult : CrepControlResult (Word 64) :=
  .returned
    { locals := updateCrepLocal (fun _ => none) 1 (BitVec.ofNat 64 7)
      memory := updateMemory (fun _ => none) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 7) }
    [BitVec.ofNat 64 7]

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
      crepeHandlerCallResult, evalCrepFullCall, evalCrepFullProg,
      evalCrepFullExps, evalCrepFullExp, assignCrepValues, assignRet,
      crepNestedSeq, loadGlobals, compileProg, compileExp,
      updateCrepLocal, updateMemory, lookupCompiledFunction, hexn]

end Flapjack
