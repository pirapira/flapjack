import Flapjack.PanItreeFfi

/-!
# Pancake `h_prog_store_32`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:297-306`.
The two expression operands are represented by optional already-evaluated
words.  `store32` is the source memory operation, including its alignment and
domain checks, and the result carries the source state through every branch.
-/

namespace Flapjack

inductive PanHProgStore32Result (σ : Type u) where
  | normal (sourceState : σ)
  | error (sourceState : σ)
  deriving Repr

def panHProgStore32 [BEq α]
    (sourceState : σ) (store32 : σ → α → α → Option σ)
    (address value : Option α) :
    PanFfiTree (PanHProgStore32Result σ) :=
  match address, value with
  | some address, some value =>
      match store32 sourceState address value with
      | some nextState => .ret (.normal nextState)
      | none => .ret (.error sourceState)
  | _, _ => .ret (.error sourceState)

@[simp] theorem panHProgStore32_invalid [BEq α]
    (sourceState : σ) (store32 : σ → α → α → Option σ)
    (address : Option α) :
    panHProgStore32 sourceState store32 address none =
      PanFfiTree.ret (α := PanHProgStore32Result σ)
        (PanHProgStore32Result.error sourceState) := by
  cases address <;> simp [panHProgStore32]

end Flapjack
