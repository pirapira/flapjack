import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.eval`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:90-143`.

`crepEval` exposes the exact runtime expression evaluator at the source
boundary.  Its branches cover constants, locals, checked loads, globals,
word operations, comparisons, shifts, and base/top addresses; invalid
subexpressions return `none` through the same `Option` computation.
-/

namespace Flapjack

def crepEval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α :=
  evalCrepRuntimeExp state

@[simp] theorem crepEval_eq_runtime
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ)
    (expression : CrepExp α) :
    crepEval state expression = evalCrepRuntimeExp state expression := by
  rfl

end Flapjack
