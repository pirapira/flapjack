import Flapjack.PanValueFfiClockCorrectness
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

def clockedMemoryFfiDecliningFinalProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext
    { memoryFfiInitial with ffi := memoryFfiFinalState } 20
    (fun _ _ => none) memoryFfiTestHandler 20
    [.function
      { name := "main", inline := false, exported := true, params := [],
        body := memoryFfiFinalMain, returnShape := .one }]
    "main" [] (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiDecliningHandler)

def clockedMemoryFfiDecliningFinalProgramIsReachable : Bool :=
  match clockedMemoryFfiDecliningFinalProgramResult with
  | some (.control (.finalFfi locals _ memory ffi event), 19) =>
      locals "x" = none && memory 200 = none && ffi.state = () &&
        event.name = .extCall "unknown" && event.outcome = .failed
  | _ => false

#guard clockedMemoryFfiDecliningFinalProgramIsReachable

def clockedRaisedDeclarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .raise "E" (.const 7), returnShape := .one }]

def clockedRaisedProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20 clockedRaisedDeclarations "main" []

def clockedRaisedProgramAccepted : Bool :=
  match clockedRaisedProgramResult with
  | some (.control (.raised locals globals memory ffi exception (.word value)), 19) =>
      exception == "E" && value == 7 && locals "x" = none &&
        globals "x" = none && memory 200 = none && ffi.state = ()
  | _ => false

#guard clockedRaisedProgramAccepted

def clockedTimeoutProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 0
    (fun _ _ => none) memoryFfiTestHandler 20 clockedRaisedDeclarations "main" []

def clockedTimeoutProgramAccepted : Bool :=
  match clockedTimeoutProgramResult with
  | some (.timeout locals globals memory ffi, 0) =>
      locals "x" = none && globals "x" = none && memory 200 = none && ffi.state = ()
  | _ => false

#guard clockedTimeoutProgramAccepted

def clockedReturnedProgramAccepted : Bool :=
  match clockedMemoryFfiResult with
  | some (.control (.returned locals _ memory _ [.word value]), 19) =>
      locals "x" = none && value == 8 &&
        match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard clockedReturnedProgramAccepted

end Flapjack
