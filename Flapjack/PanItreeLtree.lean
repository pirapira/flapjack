import Flapjack.PanItreeFfi

/-!
# Pancake `ltree`

This is the finite productive expansion of
`cakeml/pancake/semantics/pan_itreeSemScript.sml:1537-1559`.
The source `ltree_def` uses `itree_iter`: `Ret` is preserved, `Tau` remains a
silent step, and every `Vis` becomes a `Tau` around the continuation. A
length-preserving return updates the host state before that continuation;
length failure and `Oracle_final` preserve the state and select their source
failure/final continuation. `panLtreeFuel` makes the source iterator's finite
unfolding explicit for executable parity checks.
-/

namespace Flapjack

def panLtreeFuel {α σ : Type} : Nat → PanFfiTree α → PanFfiWorld σ → PanFfiTree α
  | 0, tree, _ => tree
  | _fuel + 1, .ret value, _ => .ret value
  | fuel + 1, .tau next, world =>
      .tau (panLtreeFuel fuel next world)
  | fuel + 1, .vis name configuration bytes k, world =>
      match world.oracle name world.state configuration bytes with
      | .returned nextState nextBytes =>
          if nextBytes.length = bytes.length then
            .tau (panLtreeFuel fuel (k (.returned nextBytes))
              { world with state := nextState })
          else
            .tau (panLtreeFuel fuel (k .failed) world)
      | .final outcome =>
          .tau (panLtreeFuel fuel (k (.final outcome)) world)

@[simp] theorem panLtreeFuel_zero (tree : PanFfiTree α) (world : PanFfiWorld σ) :
    panLtreeFuel 0 tree world = tree := by
  rfl

@[simp] theorem panLtreeFuel_ret (fuel : Nat) (value : α)
    (world : PanFfiWorld σ) :
    panLtreeFuel fuel.succ (.ret value) world = .ret value := by
  simp [panLtreeFuel]

@[simp] theorem panLtreeFuel_tau (fuel : Nat) (tree : PanFfiTree α)
    (world : PanFfiWorld σ) :
    panLtreeFuel fuel.succ (.tau tree) world =
      .tau (panLtreeFuel fuel tree world) := by
  simp [panLtreeFuel]

theorem panLtreeFuel_vis_return (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8)
    (k : PanFfiResponse → PanFfiTree α) (world : PanFfiWorld σ)
    (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes)
    (hlength : nextBytes.length = bytes.length) :
    panLtreeFuel fuel.succ (.vis name configuration bytes k) world =
      .tau (panLtreeFuel fuel (k (.returned nextBytes))
        { world with state := nextState }) := by
  simp [panLtreeFuel, horacle, hlength]

theorem panLtreeFuel_vis_length_failure (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8)
    (k : PanFfiResponse → PanFfiTree α) (world : PanFfiWorld σ)
    (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes)
    (hlength : nextBytes.length ≠ bytes.length) :
    panLtreeFuel fuel.succ (.vis name configuration bytes k) world =
      .tau (panLtreeFuel fuel (k .failed) world) := by
  simp [panLtreeFuel, horacle, hlength]

theorem panLtreeFuel_vis_final (fuel : Nat) (name : FfiName)
    (configuration bytes : List UInt8) (k : PanFfiResponse → PanFfiTree α)
    (world : PanFfiWorld σ) (outcome : FfiOutcome)
    (horacle : world.oracle name world.state configuration bytes =
      .final outcome) :
    panLtreeFuel fuel.succ (.vis name configuration bytes k) world =
      .tau (panLtreeFuel fuel (k (.final outcome)) world) := by
  simp [panLtreeFuel, horacle]

end Flapjack
