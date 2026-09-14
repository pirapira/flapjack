import Flapjack.PanItreeFfi

/-!
# Pancake `trace_prefix`

This is the finite, productive observation of
`cakeml/pancake/semantics/pan_itreeSemScript.sml:1639-1653`.
The source definition uses `LUNFOLD`/`LFLATTEN`; `tracePrefixFuel` exposes the
same transition order at a finite observation depth. `Tau` contributes no
event, a length-preserving `Oracle_return` contributes one `FfiEvent` and
updates the host state before continuing, and a length mismatch or
`Oracle_final` continues without emitting an event.
-/

namespace Flapjack

def tracePrefixEvent (name : FfiName) (configuration bytes nextBytes : List UInt8) :
    FfiEvent :=
  { name := name
    configuration := configuration
    bytes := bytes.zip nextBytes }

def tracePrefixFuel {α σ : Type} : Nat → PanFfiTree α → PanFfiWorld σ →
    Option (List FfiEvent)
  | _, .ret _, _ => some []
  | 0, .tau _, _ => none
  | 0, .vis _ _ _ _, _ => none
  | fuel + 1, .tau next, world =>
      tracePrefixFuel fuel next world
  | fuel + 1, .vis name configuration bytes k, world =>
      match world.oracle name world.state configuration bytes with
      | .returned nextState nextBytes =>
          if nextBytes.length = bytes.length then
            match tracePrefixFuel fuel (k (.returned nextBytes))
                { world with state := nextState } with
            | some events =>
                some (tracePrefixEvent name configuration bytes nextBytes :: events)
            | none => none
          else
            tracePrefixFuel fuel (k .failed) world
      | .final outcome =>
          tracePrefixFuel fuel (k (.final outcome)) world

@[simp] theorem tracePrefixFuel_ret (fuel : Nat) (value : α)
    (world : PanFfiWorld σ) :
    tracePrefixFuel fuel (.ret value) world = some [] := by
  simp [tracePrefixFuel]

@[simp] theorem tracePrefixFuel_tau (fuel : Nat) (tree : PanFfiTree α)
    (world : PanFfiWorld σ) :
    tracePrefixFuel fuel.succ (.tau tree) world =
      tracePrefixFuel fuel tree world := by
  simp [tracePrefixFuel]

theorem tracePrefixFuel_vis_return (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8)
    (k : PanFfiResponse → PanFfiTree α) (world : PanFfiWorld σ)
    (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes)
    (hlength : nextBytes.length = bytes.length) :
    tracePrefixFuel fuel.succ (.vis name configuration bytes k) world =
      match tracePrefixFuel fuel (k (.returned nextBytes))
          { world with state := nextState } with
      | some events =>
          some (tracePrefixEvent name configuration bytes nextBytes :: events)
      | none => none := by
  simp [tracePrefixFuel, horacle, hlength]

theorem tracePrefixFuel_vis_length_failure (fuel : Nat) (name : FfiName)
    (configuration bytes nextBytes : List UInt8)
    (k : PanFfiResponse → PanFfiTree α) (world : PanFfiWorld σ)
    (nextState : σ)
    (horacle : world.oracle name world.state configuration bytes =
      .returned nextState nextBytes)
    (hlength : nextBytes.length ≠ bytes.length) :
    tracePrefixFuel fuel.succ (.vis name configuration bytes k) world =
      tracePrefixFuel fuel (k .failed) world := by
  simp [tracePrefixFuel, horacle, hlength]

theorem tracePrefixFuel_vis_final (fuel : Nat) (name : FfiName)
    (configuration bytes : List UInt8) (k : PanFfiResponse → PanFfiTree α)
    (world : PanFfiWorld σ) (outcome : FfiOutcome)
    (horacle : world.oracle name world.state configuration bytes =
      .final outcome) :
    tracePrefixFuel fuel.succ (.vis name configuration bytes k) world =
      tracePrefixFuel fuel (k (.final outcome)) world := by
  simp [tracePrefixFuel, horacle]

/-! `trace_prefix0_def` uses the same observable transition machine but the
result is the unwrapped `itree_evaluate` sum: `Oracle_return` continues with
the returned bytes directly, while `Oracle_final` and length failure continue
with their direct terminal outcomes. `PanFfiResponse` is already this
normalized result representation, so its finite observation is this wrapper
over the shared transition equations. -/
def tracePrefix0Fuel {α σ : Type} (fuel : Nat) (tree : PanFfiTree α)
    (world : PanFfiWorld σ) : Option (List FfiEvent) :=
  tracePrefixFuel fuel tree world

@[simp] theorem tracePrefix0Fuel_eq_tracePrefixFuel (fuel : Nat)
    (tree : PanFfiTree α) (world : PanFfiWorld σ) :
    tracePrefix0Fuel fuel tree world = tracePrefixFuel fuel tree world := by
  rfl

end Flapjack
