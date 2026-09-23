import Flapjack.Pancake.Semantics.CrepSem

/-!
# Pancake `crepSem.eval`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:90-166`.

This module gives a direct recursive interpretation of the Crepe expression
constructors over the runtime state's word-valued representation. Its `Var`
equation is exactly HOL `crepSem.eval`'s `FLOOKUP s.locals v` clause and is the
only evaluator case used by `lookup_locals_eq_map_vars`. The runtime state
stores memory as a partial map rather than HOL's total memory plus domain, so
this evaluator is not tagged as a whole-definition port of `eval_def`. It is
independent of both `evalCrepRuntimeExp` and the legacy compatibility
evaluator `evalCrepFullExpState` from `CrepeSemantics`.
-/

namespace Flapjack

def crepSemEvalExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address => do
      let address ← crepSemEvalExp state address
      crepRuntimeLoad state address
  | .load32 address => do
      let address ← crepSemEvalExp state address
      crepRuntimeLoad32 state address
  | .loadByte address => do
      let address ← crepSemEvalExp state address
      crepRuntimeLoadByte state address
  | .loadGlob address => state.globals address
  | .op operator expressions => do
      let values ← expressions.mapM (crepSemEvalExp state)
      state.memoryModel.wordOp operator values
  | .crepOp .mul [left, right] => do
      let left ← crepSemEvalExp state left
      let right ← crepSemEvalExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← crepSemEvalExp state left
      let right ← crepSemEvalExp state right
      pure (state.memoryModel.compare operator left right)
  | .shift operator left right => do
      let left ← crepSemEvalExp state left
      let right ← crepSemEvalExp state right
      state.memoryModel.shift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

/-- HOL `crepSem.eval s (Var v)` is `FLOOKUP s.locals v`; this is the
directly translated variable equation used by the tagged
`lookup_locals_eq_map_vars` port. -/
@[simp] theorem crepSemEvalExp_var
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (name : Nat) :
    crepSemEvalExp state (.var name) = state.locals name := by
  simp [crepSemEvalExp]

end Flapjack
