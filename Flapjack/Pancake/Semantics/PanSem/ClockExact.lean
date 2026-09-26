import Flapjack.Pancake.Semantics.PanSem.ControlExact
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact
import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.CallExact

/-!
# Exact `panSem` clock bounds for the recursive `evaluate` dispatcher

HOL `panSemScript.sml` proves:

* `fix_clock_IMP_LESS_EQ` (`:451-457`):
  `!x. fix_clock s x = (res,s1) ==> s1.clock <= s.clock`.
* `evaluate_clock` (`:755-766`):
  `!prog s r s'. evaluate (prog,s) = (r,s') ==> s'.clock <= s.clock`.
* `fix_clock_evaluate` (`:768-775`): `fix_clock s (evaluate (prog,s)) = evaluate (prog,s)`.

The function-backed rendering below is `fix_clock_IMP_LESS_EQ` over the
`mlstring`-keyed `PanSemStateExact` record. Its theorem tag is withheld because
that record has unrestricted lookup-function fields where HOL `state` has
finite-map fields. HOL `evaluate_clock` has exactly the hypothesis
`evaluate (prog,s) = (r,s')` and concludes `s'.clock <= s.clock`; it adds no
fuel, evaluator-totality, or state-invariant premise. The Lean clock-bound
interfaces below instead take a supplied evaluator and a clock-bound
hypothesis, so they do not prove this whole-evaluator implication.
`evaluate_clock`/`fix_clock_evaluate` mention the recursive `evaluate` itself.
The currently available `evalHOLFinite` is a clause-shaped expression
rendering over `PanSemStateFiniteExact`, but it delegates to `evalHOLExact` and
is not the total recursive statement evaluator quantified by these theorems;
the total dispatcher is still being assembled under
`flapjack-pxn.18.4.3.77.2`. Also, `fix_clock_evaluate` states equality of the
whole `(result, state)` pair after clamping the post-state clock, not merely a
bound on one helper call. Therefore neither theorem is tagged or proved from
the partial/Option-valued dispatcher. The faithful finite-map theorem follow-up
is `flapjack-pxn.18.4.3.77.2.8`; source inventory dispositions are recorded in
`flapjack-4ac.3.48` (`evaluate_clock`) and `flapjack-4ac.3.49`
(`fix_clock_evaluate`).

The remaining declarations are an untagged clock-bound interface for that
dispatcher: every exact clause step (`Tick`, `If`, `Seq`, `While`) and every
state update (`empty_locals`, `dec_clock`, `set_var`, `set_kvar`) is shown to
keep the state clock under the incoming clock, under explicit hypotheses for the
recursive calls. These mirror the shape the dispatcher's measure argument needs
and are interfaces for the remaining total-evaluator assembly.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- Clock bound for the exact `fix_clock`: the clamped clock never increases. -/
theorem fixClockHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (state : PanSemStateExact width σ) (step : β × PanSemStateExact width σ) :
    (fixClockHOLExact state step).2.clock ≤ state.clock := by
  obtain ⟨result, state1⟩ := step
  simp only [fixClockHOLExact]
  split <;> omega

/-- Function-backed rendering of HOL `fix_clock_IMP_LESS_EQ`
    (`panSemScript.sml:451-457`); untagged because the state map fields are not
    constrained to finite support. The exact finite-support replacement over
    `PanSemStateFiniteExact` is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.5`
    (parent `.2.3`). -/
theorem fixClockHOLExact_IMP_LESS_EQ {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (state : PanSemStateExact width σ) (result : β) (state1 : PanSemStateExact width σ)
    (step : β × PanSemStateExact width σ)
    (h : fixClockHOLExact state step = (result, state1)) :
    state1.clock ≤ state.clock := by
  have hle := fixClockHOLExact_clock_le state step
  rw [h] at hle
  exact hle

/-- Untagged: `empty_locals` keeps the clock. -/
@[simp] theorem emptyLocalsHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).clock ≤ state.clock := Nat.le_refl _

/-- Untagged: `dec_clock` does not increase the clock. -/
theorem decClockHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (decClockHOLExact state).clock ≤ state.clock := by
  simp only [decClockHOLExact]
  omega

/-- Untagged: `set_var` keeps the clock. -/
@[simp] theorem setVarHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ) :
    (setVarHOLExact name value state).clock = state.clock := rfl

/-- Untagged: `set_kvar` keeps the clock. -/
@[simp] theorem setKvarHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) :
    (setKvarHOLExact kind name value state).clock = state.clock := by
  cases kind <;> rfl

/-- Untagged: the exact `Tick` step does not increase the clock. -/
theorem tickStepHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (tickStepHOLExact state).2.clock ≤ state.clock := by
  simp only [tickStepHOLExact]
  split
  · simp [emptyLocalsHOLExact]
  · exact decClockHOLExact_clock_le state

/-- Untagged: the exact `If` step keeps the clock under the bound for the
branch evaluator. -/
theorem ifStepHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (hbound : ∀ (program : ProgHOL width) (state : PanSemStateExact width σ),
      (evaluate program state).2.clock ≤ state.clock) :
    (ifStepHOLExact state condition thenBranch elseBranch evalExpression evaluate).2.clock
      ≤ state.clock := by
  simp only [ifStepHOLExact]
  split
  · exact hbound _ _
  · exact Nat.le_refl _

/-- Untagged: the exact `Seq` step keeps the clock under the bound for the
evaluator. -/
theorem seqStepHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (first second : ProgHOL width)
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (hbound : ∀ (program : ProgHOL width) (state : PanSemStateExact width σ),
      (evaluate program state).2.clock ≤ state.clock) :
    (seqStepHOLExact state first second evaluate).2.clock ≤ state.clock := by
  simp only [seqStepHOLExact]
  cases hresult : (fixClockHOLExact state (evaluate first state)).1 with
  | none =>
      exact Nat.le_trans (hbound second _) (fixClockHOLExact_clock_le state (evaluate first state))
  | some result =>
      exact fixClockHOLExact_clock_le state (evaluate first state)

/-- Untagged: the exact `While` step keeps the clock under the bounds for the
body evaluator and the recursive `While` call. -/
theorem whileStepHOLExact_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (recurseWhile : PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (hrecurse : ∀ state : PanSemStateExact width σ,
      (recurseWhile state).2.clock ≤ state.clock) :
    (whileStepHOLExact state condition body evalExpression evaluate recurseWhile).2.clock
      ≤ state.clock := by
  simp only [whileStepHOLExact]
  split
  · split
    · split
      · simp [emptyLocalsHOLExact]
      · have hfix := fixClockHOLExact_clock_le (decClockHOLExact state)
          (evaluate body (decClockHOLExact state))
        split
        · exact Nat.le_trans (hrecurse _) (Nat.le_trans hfix (decClockHOLExact_clock_le state))
        · exact Nat.le_trans (hrecurse _) (Nat.le_trans hfix (decClockHOLExact_clock_le state))
        · exact Nat.le_trans hfix (decClockHOLExact_clock_le state)
        · exact Nat.le_trans hfix (decClockHOLExact_clock_le state)
    · simp
  · simp

end Flapjack
