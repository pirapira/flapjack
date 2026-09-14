import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.eval`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:90-166`.

The executable Crepe runtime already evaluates the same expression cases
against checked memory, globals, target word operations, comparisons, shifts,
and base/top addresses.  This source-shaped name exposes that boundary for
the source parity suite without introducing a second evaluator.
-/

namespace Flapjack

def crepSemEvalExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α :=
  evalCrepRuntimeExp state

@[simp] theorem crepSemEvalExp_eq_runtime
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (expression : CrepExp α) :
    crepSemEvalExp state expression = evalCrepRuntimeExp state expression := by
  rfl

end Flapjack
