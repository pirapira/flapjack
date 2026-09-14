import Flapjack.PanItreeFfi

/-!
# Pancake `itree_evaluate`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:582-594`.
This is the source-shaped `itree_unfold` boundary after `mrec h_prog` has
produced a tree.  A normal terminal carries `(result option, bstate)` and
projects the result; an FFI-side terminal maps to `Error`.  Silent and visible
steps remain in the same order, with visible continuations transformed
recursively.
-/

namespace Flapjack

inductive PanItreeEvaluateResult (α : Type u) (σ : Type v) where
  | result (value : Option α) (sourceState : σ)
  | error (sourceState : σ)
  deriving DecidableEq, Repr

abbrev PanItreeEvaluateTerminal (α : Type u) (σ : Type v) :=
  Sum (Sum FfiOutcome (List UInt8)) (Option α × σ)

def panItreeEvaluate {α : Type u} {σ : Type v} (sourceState : σ) :
    PanFfiTree (PanItreeEvaluateTerminal α σ) →
      PanFfiTree (PanItreeEvaluateResult α σ)
  | .ret (.inl _) => .ret (.error sourceState)
  | .ret (.inr (value, state)) => .ret (.result value state)
  | .tau next => .tau (panItreeEvaluate sourceState next)
  | .vis name configuration bytes k =>
      .vis name configuration bytes
        (fun response => panItreeEvaluate sourceState (k response))

@[simp] theorem panItreeEvaluate_ret_error {α σ : Type u}
    (sourceState : σ) (outcome : Sum FfiOutcome (List UInt8)) :
    panItreeEvaluate sourceState (α := α) (σ := σ)
        (.ret (.inl outcome) : PanFfiTree (PanItreeEvaluateTerminal α σ)) =
      PanFfiTree.ret (α := PanItreeEvaluateResult α σ) (.error sourceState) := by
  rfl

@[simp] theorem panItreeEvaluate_ret_result {α σ : Type u}
    (value : Option α) (state sourceState : σ) :
    panItreeEvaluate sourceState (α := α) (σ := σ)
        (.ret (.inr (value, state)) : PanFfiTree (PanItreeEvaluateTerminal α σ)) =
      PanFfiTree.ret (α := PanItreeEvaluateResult α σ) (.result value state) := by
  rfl

end Flapjack
