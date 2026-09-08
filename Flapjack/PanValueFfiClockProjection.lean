import Flapjack.PanValueFfiClockCorrectness

/-!
# Clocked-to-stepped source projection

This file provides the first compositional bridge between the explicit-clock
stateful-FFI evaluator and the source-step evaluator.  The hypotheses expose
the agreement at the two component boundaries; the conclusion preserves both
the clocked result and the exact accumulated source-step count across `seq`.
-/

namespace Flapjack

theorem evalPanValueFfiClockProg_seq_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock firstClock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (middleLocals middleGlobals : VarName → Option (PanValue α))
    (middleMemory : α → Option (PanValue α)) (middleFfi : FfiState σ)
    (secondResult : PanValueFfiControlResult α σ)
    (firstSteps secondSteps : Nat)
    (first second : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hfirstClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi clock first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.normal middleLocals middleGlobals middleMemory middleFfi), firstClock))
    (hsecondClock : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi firstClock second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock))
    (hfirstSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel locals globals memory ffi first
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.normal middleLocals middleGlobals middleMemory middleFfi, firstSteps))
    (hsecondSteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel middleLocals middleGlobals middleMemory
      middleFfi second (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, secondSteps)) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control secondResult, finalClock) ∧
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.seq first second) (memoryAccess := memoryAccess) (contracts := contracts) =
      some (secondResult, firstSteps + secondSteps + 1) := by
  constructor
  · simp [evalPanValueFfiClockProg, hfirstClock, hsecondClock]
  · simp [evalPanValueFfiProgSteps, hfirstSteps, hsecondSteps]

end Flapjack
