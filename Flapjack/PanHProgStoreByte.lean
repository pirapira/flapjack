import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_store_byte`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:287-296`.
The expression evaluation is represented by already-evaluated optional word
operands, while `storeByte` is the explicit source memory projection.  A
successful store returns its updated state; failed storage and invalid
operands return `Error` with the original state.
-/

namespace Flapjack

inductive PanHProgStoreByteResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  deriving Repr

def panHProgStoreByte [BEq α]
    (sourceState : σ) (storeByte : σ → α → α → Option σ)
    (byteValue : α → α) (address value : Option α) :
    PanFfiTree (PanHProgStoreByteResult σ) :=
  match address, value with
  | some address, some value =>
      match storeByte sourceState address (byteValue value) with
      | some nextState => .ret (.normal nextState)
      | none => .ret (.error sourceState)
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgStoreByte_invalid [BEq α]
    (sourceState : σ) (storeByte : σ → α → α → Option σ)
    (byteValue : α → α) (address : Option α) :
    panHProgStoreByte sourceState storeByte byteValue address none =
      PanFfiTree.ret (α := PanHProgStoreByteResult σ)
        (PanHProgStoreByteResult.error sourceState) := by
  cases address <;> simp [panHProgStoreByte]

end Flapjack
