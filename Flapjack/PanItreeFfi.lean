import Flapjack.Ffi

/-!
# Pancake `comp_ffi`

This is the source-shaped finite observation of
`cakeml/pancake/semantics/pan_itreeSemScript.sml:1574-1589`.  Pancake's
`comp_ffi` is a `WHILE` over `Ret`, `Tau`, and `Vis`: `Tau` preserves the FFI
state, and `Vis` applies the oracle, changing the state only for a
length-preserving `Oracle_return`.  A finite fuel argument makes the partial
HOL `WHILE` executable in Lean; a terminating source computation agrees with
`compFfi` once the fuel exceeds its number of transitions.
-/

namespace Flapjack

inductive PanFfiResponse where
  | returned (bytes : List UInt8)
  | failed
  | final (outcome : FfiOutcome)
  deriving DecidableEq, Repr

inductive PanFfiTree (α : Type u) where
  | ret (value : α)
  | tau (next : PanFfiTree α)
  | vis (name : FfiName) (configuration bytes : List UInt8)
      (k : PanFfiResponse → PanFfiTree α)

structure PanFfiWorld (σ : Type u) where
  oracle : FfiOracle σ
  state : σ

abbrev PanFfiStep (α σ : Type) :=
  Option (PanFfiTree α × PanFfiWorld σ)

/-- Executable finite observation of the source `comp_ffi` `WHILE`. -/
def compFfiFuel {α σ : Type} : Nat → PanFfiTree α → PanFfiWorld σ → PanFfiStep α σ
  | _, .ret value, world => some (.ret value, world)
  | 0, .tau _, _ => none
  | 0, .vis _ _ _ _, _ => none
  | fuel + 1, .tau next, world => compFfiFuel fuel next world
  | fuel + 1, .vis name configuration bytes k, world =>
      match world.oracle name world.state configuration bytes with
      | .returned nextState nextBytes =>
          if nextBytes.length = bytes.length then
            compFfiFuel fuel (k (.returned nextBytes))
              { world with state := nextState }
          else
            compFfiFuel fuel (k .failed) world
      | .final outcome =>
          compFfiFuel fuel (k (.final outcome)) world

def compFfi {α σ : Type} (fuel : Nat) (tree : PanFfiTree α)
    (world : PanFfiWorld σ) : PanFfiStep α σ :=
  compFfiFuel fuel tree world

@[simp] theorem compFfi_ret (fuel : Nat) (value : α) (world : PanFfiWorld σ) :
    compFfi fuel (.ret value) world = some (.ret value, world) := by
  simp [compFfi, compFfiFuel]

@[simp] theorem compFfi_tau (fuel : Nat) (next : PanFfiTree α)
    (world : PanFfiWorld σ) :
    compFfi fuel.succ (.tau next) world = compFfi fuel next world := by
  simp [compFfi, compFfiFuel]

theorem compFfi_vis_return (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8) (k : PanFfiResponse → PanFfiTree α)
    (world : PanFfiWorld σ) (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes) (hlength : nextBytes.length = bytes.length) :
    compFfi fuel.succ (.vis name configuration bytes k) world =
      compFfi fuel (k (.returned nextBytes)) { world with state := nextState } := by
  cases fuel <;> simp [compFfi, compFfiFuel, horacle, hlength]

theorem compFfi_vis_length_failure (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8) (k : PanFfiResponse → PanFfiTree α)
    (world : PanFfiWorld σ) (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes) (hlength : nextBytes.length ≠ bytes.length) :
    compFfi fuel.succ (.vis name configuration bytes k) world =
      compFfi fuel (k .failed) world := by
  cases fuel <;> simp [compFfi, compFfiFuel, horacle, hlength]

theorem compFfi_vis_final (fuel : Nat) (name : FfiName)
    (configuration bytes : List UInt8) (k : PanFfiResponse → PanFfiTree α)
    (world : PanFfiWorld σ) (outcome : FfiOutcome)
    (horacle : world.oracle name world.state configuration bytes = .final outcome) :
    compFfi fuel.succ (.vis name configuration bytes k) world =
      compFfi fuel (k (.final outcome)) world := by
  cases fuel <;> simp [compFfi, compFfiFuel, horacle]

end Flapjack
