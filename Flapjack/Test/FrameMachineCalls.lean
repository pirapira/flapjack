import Flapjack.Test.StackFrameMachine

/-!
Regression coverage for the generalized FrameMachine call equations.  The
callees are compound programs rather than a single `.raise` or `.return`, so
the tests exercise the evaluated callee-state boundary used by handler-aware
Word-to-Stack simulations.
-/

namespace Flapjack.RiscV

def generalRaiseCallCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 7 5) (.raise 7))
  | _ => none

def generalReturnCallCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.const 6 17) (.return 6))
  | _ => none

/- These tests exercise the valid Cake frame boundary rather than entering a
   linked section as a raw RISC-V function.  In particular, the default
   handler's nested FFI and the normal return continuation both run with the
   callee state that the frame protocol supplies. -/
def handlerFrameFfi : StackFrameMachineFfiHandler 64 :=
  fun function _ _ _ _ state =>
    if function = "callee" then
      some (stackFrameWriteRegister state 3 (BitVec.ofNat 64 4))
    else if function = "continuation" then
      some (stackFrameWriteRegister state 3 (BitVec.ofNat 64 5))
    else if function = "handler" then
      some (stackFrameWriteRegister state 3 (BitVec.ofNat 64 6))
    else none

def handlerFrameRaiseCode : Nat → Option (StackProg Nat)
  | 0 => some (.raise 7)
  | _ => none

def handlerFrameReturnCode : Nat → Option (StackProg Nat)
  | 0 => some (.seq (.ffi "callee" 0 0 0 0 0) (.return 3))
  | _ => none

example :
    evalStackFrameFuelWithCodeAndFfi handlerFrameFfi 32
      handlerFrameRaiseCode frameMachineState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0)
        (some ((.seq (.ffi "handler" 0 0 0 0 0) (.return 3)), 7, 0))) =
      some (.returned
        (stackFrameWriteRegister frameMachineState 3 (BitVec.ofNat 64 6))
        (BitVec.ofNat 64 6)) := by
  simp [evalStackFrameFuelWithCodeAndFfi, handlerFrameFfi,
    evalStackFrameFuelWithCode, handlerFrameRaiseCode, frameMachineState,
    stackFrameWriteRegister,
    wordStackMachineWriteRegister]

example :
    evalStackFrameFuelWithCodeAndFfi handlerFrameFfi 32
      handlerFrameReturnCode frameMachineState
      (.call (some ((.seq (.ffi "continuation" 0 0 0 0 0) (.return 3)),
          0, 0, 0)) (.label 0)
        (some ((.skip : StackProg Nat), 7, 0))) =
      some (.returned
        (stackFrameWriteRegister frameMachineState 3 (BitVec.ofNat 64 5))
        (BitVec.ofNat 64 5)) := by
  simp [evalStackFrameFuelWithCodeAndFfi, handlerFrameFfi,
    evalStackFrameFuelWithCode, handlerFrameReturnCode, frameMachineState,
    stackFrameWriteRegister,
    wordStackMachineWriteRegister]
  funext current
  by_cases h : current = 3 <;> simp [h]

example :
    evalStackFrameFuelWithCodeAndFfi identityFrameFfi 12
      generalRaiseCallCode frameMachineState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0)
        (some ((.const 3 9 : StackProg Nat), 3, 0))) =
      evalStackFrameFuelWithCodeAndFfi identityFrameFfi 11
        generalRaiseCallCode
        (stackFrameWriteRegister
          (stackFrameWriteRegister frameMachineState 7 (BitVec.ofNat 64 5))
          3 (BitVec.ofNat 64 5))
        (.const 3 9) := by
  apply evalStackFrameFuelWithCodeAndFfi_call_raise_handler_of_eval
  · rfl
  · rfl

example :
    evalStackFrameFuelWithCodeAndFfi identityFrameFfi 12
      generalReturnCallCode frameMachineState
      (.call (some ((.skip : StackProg Nat), 0, 0, 0)) (.label 0) none) =
      evalStackFrameFuelWithCodeAndFfi identityFrameFfi 11
        generalReturnCallCode
        (stackFrameWriteRegister frameMachineState 6 (BitVec.ofNat 64 17))
        (.skip) := by
  apply evalStackFrameFuelWithCodeAndFfi_call_return_handler_of_eval
  · rfl
  · rfl

end Flapjack.RiscV
