import Flapjack.Pancake.Semantics.PanSem

/-!
# Source-state `Call` entrypoint

This entrypoint is the restricted `Call` case for a code-bearing CakeML
`panSem$state`. It resolves the requested function from `state.code` and
constructs the one-entry table consumed by the existing clocked call engine
from that exact map result. It accepts only a callee body of the form
`Return e`; this makes the boundary useful for direct calls without silently
dropping other entries needed by nested calls. The general recursive
code-map evaluator, including `DecCall`, remains open.
-/

namespace Flapjack

/-- Result together with the source code map carried across evaluation. The
    call engine only returns the changing execution components, so this
    wrapper records the unchanged source-owned code field alongside it. -/
structure PanSemCodeCallResult (α : Type u) (σ : Type v) where
  evaluation : Option (PanValueFfiClockResult α σ)
  code : FunName → Option (List (VarName × Shape) × Prog α × Shape)

/-- Evaluate a direct source `Call` whose callee body is `Return e`.

The sole function table passed to the compatibility call engine is derived
from `state.code function`; it is not an independent premise. Parameter
names/shapes and return shape are copied from that same code entry and are
checked by the existing call engine. The source state supplies locals,
globals, memory, FFI, clock, structs, and addresses. -/
def panSemEvaluateCodeReturnCall
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (fuel : Nat)
    (state : PanSemState α (FfiState σ))
    (function : FunName) (arguments : List (Exp α)) :
    PanSemCodeCallResult α σ := Id.run do
  let some (parameters, body, returnShape) := state.code function
    | return { evaluation := none, code := state.code }
  let .return _ := body
    | return { evaluation := none, code := state.code }
  let contracts := some (PanValueCallContracts.mk
    [(function, returnShape)] [] [(function, parameters)])
  let functions : List (FunName × List VarName × Prog α) :=
    [(function, parameters.map Prod.fst, body)]
  let evaluation := evalPanValueFfiClockCall context primitive handler
    state.structs functions state.baseAddress state.topAddress bytesInWord fuel
    state.locals state.globals state.memory state.ffi state.clock none function arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
  return { evaluation := evaluation, code := state.code }

@[simp] theorem panSemEvaluateCodeReturnCall_preserves_code
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (memoryAccess : Option (PanValueMemoryAccess α))
    (fuel : Nat) (state : PanSemState α (FfiState σ))
    (function : FunName) (arguments : List (Exp α)) :
    (panSemEvaluateCodeReturnCall context primitive handler bytesInWord
      memoryAccess fuel state function arguments).code = state.code := by
  unfold panSemEvaluateCodeReturnCall
  cases hcode : state.code function with
  | none => simp
  | some entry => cases entry with
    | mk parameters bodyShape => cases bodyShape with
      | mk body returnShape => cases body <;> simp

end Flapjack
