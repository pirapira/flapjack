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

end Flapjack
