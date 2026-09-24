import Flapjack.Pancake.Semantics.CrepSem.Eval

/-!
# Total HOL-shaped Crep clock leaves

This module ports only the four leaf clauses `Skip`, `Break`, `Continue`, and
`Tick` of `crepSem$evaluate_def` to the 11-field `CrepHolState`. The restricted
syntax makes the implemented domain explicit: this is not a whole-program
evaluator, and it assigns no behavior to the remaining `CrepProg` constructors.
The result carrier is `option crepSem$result`, so ordinary completion is `none`
and the control results retain their HOL constructors.
-/

namespace Flapjack

/-- The four nonrecursive `evaluate_def` forms handled by this first total
    Crep evaluator slice. `toCrepProg` records their exact source constructors. -/
inductive CrepClockLeaf where
  | skip
  | breakAt (label : Nat)
  | continueAt (label : Nat)
  | tick
  deriving DecidableEq, Repr

/-- Embed a clock leaf into the production Crep syntax. -/
def CrepClockLeaf.toCrepProg {width : Nat} :
    CrepClockLeaf → CrepProg (BitVec width)
  | .skip => .skip
  | .breakAt label => .break label
  | .continueAt label => .continue label
  | .tick => .tick

/-- Total result/state equations for the four matching HOL `evaluate_def`
    constructors. This restricted function deliberately has no `Option` fuel
    wrapper and does not depend on `evalCrepRuntimeResult`. -/
def evalCrepClockLeaf {width : Nat} {σ : Type _}
    (leaf : CrepClockLeaf) (state : CrepHolState (BitVec width) σ) :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ :=
  match leaf with
  | .skip => (none, state)
  | .breakAt label => (some (.break label), state)
  | .continueAt label => (some (.continue label), state)
  | .tick =>
      if state.clock = 0 then
        (some .timeOut, emptyCrepHolLocals state)
      else
        (none, decCrepHolClock state)

@[simp] theorem evalCrepClockLeaf_skip {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf .skip state = (none, state) := rfl

@[simp] theorem evalCrepClockLeaf_break {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.breakAt label) state = (some (.break label), state) := rfl

@[simp] theorem evalCrepClockLeaf_continue {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.continueAt label) state =
      (some (.continue label), state) := rfl

theorem evalCrepClockLeaf_tick_zero {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockLeaf .tick state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockLeaf, hclock]

theorem evalCrepClockLeaf_tick_positive {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockLeaf .tick state = (none, decCrepHolClock state) := by
  simp [evalCrepClockLeaf, hclock]

end Flapjack
