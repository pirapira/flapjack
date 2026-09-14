import Flapjack.PanValues
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_raise`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:445-454`.
The expression evaluator and exception-shape lookup are represented by their
already-computed `Option` inputs.  The boundary preserves the source shape
check and 32-word limit, returning a raised value through the explicit
`emptyState` projection and `Error` with the original state otherwise.
-/

namespace Flapjack

inductive PanHProgRaiseResult (α : Type u) (σ : Type v) where
  | raised (sourceState : σ) (exception : ExceptionId) (value : PanValue α)
  | error (sourceState : σ)
  deriving Repr

def panHProgRaise [BEq String]
    (structs : StructContext) (sourceState emptyState : σ)
    (exception : ExceptionId) (exceptionShape : Option Shape)
    (value : Option (PanValue α)) :
    PanFfiTree (PanHProgRaiseResult α σ) :=
  match exceptionShape, value with
  | some expectedShape, some value =>
      let actualShape := panValueShape structs value
      if panShapeMatches actualShape expectedShape &&
          shapeSizeWithContext structs actualShape ≤ 32 then
        .ret (.raised emptyState exception value)
      else
        .ret (.error sourceState)
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgRaise_invalid [BEq String]
    (structs : StructContext) (sourceState emptyState : σ)
    (exception : ExceptionId) (exceptionShape : Option Shape) :
    panHProgRaise structs sourceState emptyState exception exceptionShape none =
      PanFfiTree.ret (α := PanHProgRaiseResult α σ)
        (PanHProgRaiseResult.error sourceState) := by
  cases exceptionShape <;> simp [panHProgRaise]

end Flapjack
