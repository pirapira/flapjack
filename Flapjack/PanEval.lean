import Flapjack.PanValues

/-!
# Pancake `eval`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:79-158`.
This source-shaped context supplies the bstate projections used by `eval_def`;
the executable expression recursion is delegated to the existing exact
`evalPanValueExp` implementation, including optional memory access handling.
-/

namespace Flapjack

structure PanEvalContext (α : Type u) where
  structs : StructContext
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)
  baseAddress : α
  topAddress : α
  bytesInWord : α

def panEval [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanEvalContext α) (expression : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValue α) :=
  evalPanValueExp context.structs context.locals context.globals context.memory
    context.baseAddress context.topAddress context.bytesInWord expression
    (memoryAccess := memoryAccess)

end Flapjack
