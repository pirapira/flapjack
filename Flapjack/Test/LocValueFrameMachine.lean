import Flapjack.StackAlloc.FrameMachine

/-! The bounded frame machine applies the same code-aware LocValue rule as the
    abstract StackAlloc machine. -/

namespace Flapjack.RiscV

def locValueFrameCode : Nat → Option (StackProg Nat)
  | 20 => some .skip
  | _ => none

example [NeZero width] (state : StackFrameMachineState width) :
    evalStackFrameFuelWithCode 1 locValueFrameCode state
      (.locValue 5 20 0) =
      some (.normal (stackFrameWriteRegister state 5
        (BitVec.ofNat width 20))) := by
  simp [evalStackFrameFuelWithCode, locValueFrameCode]

example [NeZero width] (state : StackFrameMachineState width) :
    evalStackFrameFuelWithCode 1 locValueFrameCode state
      (.locValue 5 21 0) = none := by
  simp [evalStackFrameFuelWithCode, locValueFrameCode]

end Flapjack.RiscV
