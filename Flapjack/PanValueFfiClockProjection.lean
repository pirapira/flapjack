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

/-! The no-destination return branch has the same projection property at a
call boundary.  Argument steps and callee steps are added by the stepped
evaluator, while the clocked evaluator returns the callee's remaining clock. -/
theorem evalPanValueFfiClockCall_returned_projects_to_steps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel clock finalClock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (function : FunName) (arguments : List (Exp α))
    (argumentSteps bodySteps : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hargsSteps : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some (values, argumentSteps))
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hclock : clock ≠ 0)
    (hreturn : panValueReturnValid structs contracts function values = true)
    (hwithin : panValueValuesWithinLimit structs values = true)
    (hclockBody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi values), finalClock))
    (hstepBody : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
      (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned bodyLocals finalGlobals finalMemory finalFfi values, bodySteps)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) ∧
    evalPanValueFfiCallSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      none function arguments (memoryAccess := memoryAccess) (contracts := contracts) =
      some (.returned (fun _ => none) finalGlobals finalMemory finalFfi values,
        argumentSteps + bodySteps) := by
  constructor
  · simp [evalPanValueFfiClockCall, hargs, hlookup, hbind, hclock, hreturn,
      hwithin, hclockBody]
  · simp [evalPanValueFfiCallSteps, hargsSteps, hlookup, hbind, hreturn,
      hwithin, hstepBody]

end Flapjack
