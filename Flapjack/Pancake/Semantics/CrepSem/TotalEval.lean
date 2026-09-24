import Flapjack.Pancake.Semantics.CrepSem.Eval

/-!
# Total HOL-shaped Crep control subset

This module ports the leaf clauses `Skip`, `Break`, `Continue`, and `Tick`,
plus recursive `If`, `Seq`, and `Return` programs over those leaves and the
`Raise` clause, from `crepSem$evaluate_def` to the 11-field `CrepHolState`. The
restricted syntax makes the implemented domain explicit: this is not a
whole-program evaluator and assigns no behavior to the remaining `CrepProg`
constructors. The result carrier is `option crepSem$result`, so ordinary
completion is `none` and control results retain their HOL constructors.
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

/-- Recursive program fragment for the total clock/control evaluator. Its
    `If` nodes use the source `CrepExp` condition, and its `Seq` nodes use the
    HOL `fix_clock` boundary between recursively evaluated programs. Return
    nodes evaluate their expression list in the current HOL state. -/
inductive CrepClockProg (width : Nat) where
  | leaf (value : CrepClockLeaf)
  | raiseException (value : BitVec width)
  | seq (first second : CrepClockProg width)
  | returnValues (values : List (CrepExp (BitVec width)))
  | ite (condition : CrepExp (BitVec width))
      (thenBranch elseBranch : CrepClockProg width)

/-- Embed the restricted recursive syntax into production Crep syntax. -/
def CrepClockProg.toCrepProg {width : Nat} :
  CrepClockProg width → CrepProg (BitVec width)
  | .leaf value => value.toCrepProg
  | .raiseException value => .raise value
  | .seq first second => .seq first.toCrepProg second.toCrepProg
  | .returnValues values => .return values
  | .ite condition thenBranch elseBranch =>
      .ite condition thenBranch.toCrepProg elseBranch.toCrepProg

/-- Total result/state equations for the matching HOL `evaluate_def` leaves,
    `If`, `Seq`, `Return`, and `Raise`. This restricted function deliberately has no
    `Option` fuel wrapper and does not depend on `evalCrepRuntimeResult`. -/
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

/-- Total recursive source-shaped evaluator for the leaf/`If`/`Seq` fragment. It
    evaluates an `If` condition in the supplied HOL state, selects the then
    branch for every nonzero word and the else branch for zero, and returns
    HOL `Error` with the unchanged state when expression evaluation fails.
    For `Seq`, it applies HOL `fix_clock` to the first post-state and only
    evaluates the second program after a normal result. No fuel, partial
    result, or branch-run assumption is exposed. -/
def evalCrepClockProg [NeZero width] {σ : Type _}
  : CrepClockProg width → CrepHolState (BitVec width) σ →
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ
  | .leaf value, state => evalCrepClockLeaf value state
  | .raiseException value, state =>
      (some (.exception value), emptyCrepHolLocals state)
  | .seq first second, state =>
      match evalCrepClockProg first state with
      | (none, firstState) =>
          evalCrepClockProg second
            (fixCrepHolClockW state
              ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
                firstState)).2
      | (some result, firstState) =>
          (some result, (fixCrepHolClockW state (some result, firstState)).2)
  | .returnValues values, state =>
      match values.mapM (evalCrepHolExpWordLab state) with
      | some words => (some (.return words), emptyCrepHolLocals state)
      | none => (some .error, state)
  | .ite condition thenBranch elseBranch, state =>
      match evalCrepHolExp state condition with
      | some value =>
          if value = 0 then evalCrepClockProg elseBranch state
          else evalCrepClockProg thenBranch state
      | none => (some .error, state)
termination_by program _state => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem evalCrepClockProg_return_success [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (words : List (PanWordLab (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = some words) :
    evalCrepClockProg (.returnValues values) state =
      (some (.return words), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_raise [NeZero width] {σ : Type _}
  (value : BitVec width) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockProg (.raiseException value) state =
      (some (.exception value), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg]

theorem evalCrepClockProg_return_error [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = none) :
    evalCrepClockProg (.returnValues values) state = (some .error, state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_seq_normal [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (hfirst : evalCrepClockProg first state = (none, firstState)) :
    evalCrepClockProg (.seq first second) state =
      evalCrepClockProg second
        (fixCrepHolClockW state
          ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
            firstState)).2 := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_control [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (result : CrepResultHOL (BitVec width) FfiFinalEvent)
    (hfirst : evalCrepClockProg first state = (some result, firstState)) :
    evalCrepClockProg (.seq first second) state =
      (some result, (fixCrepHolClockW state (some result, firstState)).2) := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_skip_break [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label : Nat) :
    evalCrepClockProg (.seq (.leaf .skip) (.leaf (.breakAt label))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_break_stops [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label nextLabel : Nat) :
    evalCrepClockProg
        (.seq (.leaf (.breakAt label)) (.leaf (.breakAt nextLabel))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_tick_zero [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    emptyCrepHolLocals, hclock]

theorem evalCrepClockProg_seq_tick_positive [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (none, decCrepHolClock state) := by
  have hnot : ¬ state.clock < state.clock - 1 := by omega
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    decCrepHolClock, hclock, hnot]

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

theorem evalCrepClockProg_ite_zero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = some 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg elseBranch state := by
  simp [evalCrepClockProg, hcondition]

theorem evalCrepClockProg_ite_nonzero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ) (value : BitVec width)
    (hcondition : evalCrepHolExp state condition = some value) (hnonzero : value ≠ 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg thenBranch state := by
  simp only [evalCrepClockProg, hcondition]
  by_cases hzero : value = 0
  · exact False.elim (hnonzero hzero)
  · rw [if_neg hzero]

theorem evalCrepClockProg_ite_error [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = none) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      (some .error, state) := by
  simp [evalCrepClockProg, hcondition]

end Flapjack
