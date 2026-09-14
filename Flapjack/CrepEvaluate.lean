import Flapjack.CrepeSemantics

/-!
# Crepe `evaluate`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:240-446`.

`evalCrepFullProg` already carries the complete executable scalar Crepe
evaluator.  This source-shaped entry point names that boundary explicitly:
the finite fuel argument is the Lean termination budget, while the returned
`CrepControlResult` carries the source state transitions and observable
control/effect results.
-/

namespace Flapjack

def crepEvaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (program : CrepProg α) : Option (CrepControlResult α) :=
  evalCrepFullProg functions primitive ffi sharedMem
    baseAddress topAddress fuel state program

@[simp] theorem crepEvaluate_eq_evalCrepFullProg
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (program : CrepProg α) :
    crepEvaluate functions primitive ffi sharedMem baseAddress topAddress
      fuel state program =
      evalCrepFullProg functions primitive ffi sharedMem
        baseAddress topAddress fuel state program := by
  rfl

end Flapjack
