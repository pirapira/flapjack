import Flapjack.PanValues
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_return`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:456-464`.
The source expression evaluator is represented here by its already-evaluated
`Option (PanValue α)` result.  The boundary preserves the source size check:
values at most 32 words return through the explicit `emptyState` projection,
while missing or oversized values return `Error` with the original state.
-/

namespace Flapjack

inductive PanHProgReturnResult (α : Type u) (σ : Type v) where
  | returned (sourceState : σ) (value : PanValue α)
  | error (sourceState : σ)
  deriving Repr

def panHProgReturn [BEq String]
    (structs : StructContext) (sourceState emptyState : σ)
    (value : Option (PanValue α)) :
    PanFfiTree (PanHProgReturnResult α σ) :=
  match value with
  | some value =>
      if shapeSizeWithContext structs (panValueShape structs value) ≤ 32 then
        .ret (.returned emptyState value)
      else
        .ret (.error sourceState)
  | none => .ret (.error sourceState)

@[simp] theorem panHProgReturn_invalid [BEq String]
    (structs : StructContext) (sourceState emptyState : σ) :
    panHProgReturn structs sourceState emptyState (α := α) none =
      PanFfiTree.ret (α := PanHProgReturnResult α σ)
        (PanHProgReturnResult.error sourceState) := by
  simp [panHProgReturn]

end Flapjack
