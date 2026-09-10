import Flapjack.PanValueFfiClockSemantics
import Flapjack.Test.PanValueMemoryFfi

/-! The clocked source evaluator must retain the accelerator-style memory FFI
    boundary.  This is the same memory-mutating handler used by the stepped
    evaluator, with the additional observable clock decrement at the call. -/

namespace Flapjack

def clockedMemoryFfiResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiAccelerator)

def clockedMemoryFfiResultHasWrite : Bool :=
  match clockedMemoryFfiResult with
  | some (.control (.returned _ _ memory _ [.word value]), 19) =>
      value == 8 && match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard clockedMemoryFfiResultHasWrite

def clockedMemoryFfiDecliningFinalResult := do
  let state ← evalPanValueDeclarations memoryFfiInitial.source
    [.function
      { name := "main", inline := false, exported := true, params := [],
        body := memoryFfiFinalMain, returnShape := .one }]
    (memoryAccess := some memoryFfiTestMemoryAccess)
  evalPanValueFfiClockCall memoryFfiTestContext (fun _ _ => none)
    memoryFfiTestHandler state.structs state.functions state.baseAddress
    state.topAddress state.bytesInWord 20 (fun _ => none) state.globals state.memory
    memoryFfiFinalState 20 none "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
      state.parameterShapes))
    (memoryHandler := some memoryFfiDecliningHandler)

def clockedMemoryFfiDecliningFinalIsReachable : Bool :=
  match clockedMemoryFfiDecliningFinalResult with
  | some (.control (.finalFfi locals _ memory ffi event), 19) =>
      locals "x" = none && memory 200 = none && ffi.state = () &&
        event.name = .extCall "unknown" && event.outcome = .failed
  | _ => false

#guard clockedMemoryFfiDecliningFinalIsReachable

end Flapjack
