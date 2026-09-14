/-!
# Pancake `mrec`

Source reference:
`cakeml/pancake/semantics/pan_itreeSemScript.sml:173-190`.

The source `mrec_def` is the `itree_iter` bridge from an interaction tree with
internal events to one whose visible events are retained.  Returns and silent
steps are preserved, an internal event invokes its handler through
`itree_bind`, and an external event remains visible while its continuation is
recursively transformed.  `panMrecFuel` is the finite executable observation
of that source-shaped transition; fuel exhaustion returns the current tree
without inventing a terminal result.
-/

namespace Flapjack

inductive PanMrecTree (answer : Type u) (ι : Type v) (ε : Type w)
    (result : Type x) where
  | ret (value : result)
  | tau (next : PanMrecTree answer ι ε result)
  | visInternal (event : ι) (k : answer → PanMrecTree answer ι ε result)
  | visExternal (event : ε) (k : answer → PanMrecTree answer ι ε result)

def panMrecBind {answer ι ε α β : Type} :
    PanMrecTree answer ι ε α →
      (α → PanMrecTree answer ι ε β) → PanMrecTree answer ι ε β
  | .ret value, continuation => continuation value
  | .tau next, continuation => .tau (panMrecBind next continuation)
  | .visInternal event k, continuation =>
      .visInternal event (fun answer => panMrecBind (k answer) continuation)
  | .visExternal event k, continuation =>
      .visExternal event (fun answer => panMrecBind (k answer) continuation)

def panMrecFuel {α ι ε : Type} :
    Nat → (ι → PanMrecTree α ι ε α) →
      PanMrecTree α ι ε α → PanMrecTree α ι ε α
  | 0, _, tree => tree
  | _fuel + 1, _handler, .ret value => .ret value
  | fuel + 1, handler, .tau next => .tau (panMrecFuel fuel handler next)
  | fuel + 1, handler, .visInternal event k =>
      .tau (panMrecFuel fuel handler (panMrecBind (handler event) k))
  | fuel + 1, handler, .visExternal event k =>
      .visExternal event (fun answer =>
        .tau (panMrecFuel fuel handler (k answer)))

@[simp] theorem panMrecFuel_zero {α ι ε : Type}
    (handler : ι → PanMrecTree α ι ε α)
    (tree : PanMrecTree α ι ε α) :
    panMrecFuel 0 handler tree = tree := by
  rfl

@[simp] theorem panMrecFuel_succ_ret {α ι ε : Type} (fuel : Nat)
    (handler : ι → PanMrecTree α ι ε α) (value : α) :
    panMrecFuel fuel.succ handler (.ret value) = .ret value := by
  simp [panMrecFuel]

@[simp] theorem panMrecFuel_succ_tau {α ι ε : Type} (fuel : Nat)
    (handler : ι → PanMrecTree α ι ε α)
    (tree : PanMrecTree α ι ε α) :
    panMrecFuel fuel.succ handler (.tau tree) =
      .tau (panMrecFuel fuel handler tree) := by
  simp [panMrecFuel]

theorem panMrecFuel_succ_internal {α ι ε : Type} (fuel : Nat)
    (handler : ι → PanMrecTree α ι ε α) (event : ι)
    (k : α → PanMrecTree α ι ε α) :
    panMrecFuel fuel.succ handler (.visInternal event k) =
      .tau (panMrecFuel fuel handler (panMrecBind (handler event) k)) := by
  simp [panMrecFuel]

theorem panMrecFuel_succ_external {α ι ε : Type} (fuel : Nat)
    (handler : ι → PanMrecTree α ι ε α) (event : ε)
    (k : α → PanMrecTree α ι ε α) :
    panMrecFuel fuel.succ handler (.visExternal event k) =
      .visExternal event (fun answer =>
        .tau (panMrecFuel fuel handler (k answer))) := by
  simp [panMrecFuel]

end Flapjack
