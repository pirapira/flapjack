import Flapjack.PanValues
import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_store`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:277-285`.

Expression evaluation is represented by its already-evaluated optional
address/value operands.  The memory callback is explicit, so the boundary
retains Pancake's `mem_stores` behavior without inventing a reduced memory
model: successful stores return the updated source state and failed or
malformed stores return `Error` with the original state.
-/

namespace Flapjack

inductive PanHProgStoreMemResult (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  deriving Repr

def panHProgStoreMem [BEq α]
    (sourceState : σ)
    (store : σ → α → List α → Option σ)
    (flatten : PanValue α → List α)
    (address : Option α) (value : Option (PanValue α)) :
    PanFfiTree (PanHProgStoreMemResult σ) :=
  match address, value with
  | some address, some value =>
      match store sourceState address (flatten value) with
      | some nextState => .ret (.normal nextState)
      | none => .ret (.error sourceState)
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgStoreMem_invalid [BEq α]
    (sourceState : σ)
    (store : σ → α → List α → Option σ)
    (flatten : PanValue α → List α) (address : Option α) :
    panHProgStoreMem sourceState store flatten address none =
      PanFfiTree.ret (α := PanHProgStoreMemResult σ)
        (PanHProgStoreMemResult.error sourceState) := by
  cases address <;> simp [panHProgStoreMem]

end Flapjack
