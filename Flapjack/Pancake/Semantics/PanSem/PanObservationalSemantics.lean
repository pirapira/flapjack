import Flapjack.Pancake.Semantics.PanSem.AddClock
import Flapjack.FfiHOL

/-!
# Pancake `panSem.semantics`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:785-809`
(`semantics_def`).  HOL repeatedly evaluates `Call NONE start []` at the
clock-indexed states `s with clock := k`, fails when some clock yields a
forbidden result, chooses a successful `Return`/`FinalFFI` witness, and
otherwise returns the `build_lprefix_lub` of the clock-indexed FFI-event
prefixes.

This module provides a Flapjack-specific observational behaviour carrier and
the clock-indexed entry evaluation by composing the recursive evaluator
`evalPanSemRecursiveCallContextHOLExact`.  That evaluator uses
`PanSemStateExact`: its `locals`, `globals`, `code`, and `eshapes` fields are
unrestricted lookup functions rather than HOL finite maps, and its evaluation
context carries `DecidablePred` witnesses for the two memory sets.  Although
`PanSemResultExact` and the FFI event types follow the HOL constructors, this
overall state/result construction is not an exact port of HOL's
`evaluate (prog, s with clock := k)` type.

-- FLAPJACK-SPECIFIC (no `@[hol]` tag): this is not an exact `@[hol]` port of
-- `panSem$semantics_def`: (a) its evaluator context carries memory-set
-- `DecidablePred` witnesses, and its state map fields are unrestricted lookup
-- functions rather than HOL finite maps; (b) the divergence result stores a
-- `PanLprefixLub` witness, not HOL's `build_lprefix_lub` result.  The clocked
-- event family is proved to be a prefix chain, so `panSemanticsExactTotal`
-- needs no caller-supplied chain hypothesis.  That proof does not establish
-- that `PanLprefixLub` is HOL's `build_lprefix_lub`; the state and LUB carrier
-- gaps remain, so no `@[hol]` tag is attached.
-- The tagged original definitions already exist on the canonical finite-map
-- state in the sibling `Semantics.lean`. Their HolBehaviour result is distinct
-- from this legacy witness-carrying behaviour; no bridge between those
-- observational carriers or production evaluator is claimed here.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ProgHOL)

/-- Outcome of a successful panSem run, mirroring HOL `semantics`'s two
successful result cases: a `Return` gives `Success`, a `FinalFFI` gives the
`FFI_outcome` of its `final_event`. -/
inductive PanSemExactOutcome where
  | success
  | ffi (outcome : HolFfiOutcome)
  deriving DecidableEq, Repr

/-- Observational behaviour of a panSem program, mirroring the HOL `semantics`
result constructors (`Fail`/`Terminate`/`Diverge`).  The divergence case uses
Flapjack's `PanLprefixLub` carrier; no equivalence with HOL's
`build_lprefix_lub` has been established. -/
inductive PanSemExactBehaviour where
  | diverge (family : Nat → List HolIoEvent) (trace : PanLprefixLub family)
  | terminate (outcome : PanSemExactOutcome) (events : List HolIoEvent)
  | fail

/-- HOL `semantics_def`'s entry program `Call NONE start []`. -/
def panEntryProgram {width : Nat} [NeZero width] (start : MlS) : ProgHOL width :=
  .call none start []

/-- The clock-indexed entry context `s with clock := k` of HOL `semantics_def`
(absolute clock replacement), keeping the base context's domain decidability. -/
def panClockContext {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (clock : Nat) :
    PanSemExactEvalContext width σ :=
  context.withState { context.state with clock := clock } rfl rfl

/-- Clock-indexed entry evaluation for `Call NONE start []` at absolute clock
    `clock`.  It returns the corresponding result and state projection using
    `PanSemStateExact`; this broad map carrier and its decidability context are
    not HOL's finite-map state. -/
def panEvaluateClock {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) (clock : Nat) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalPanSemRecursiveCallContextHOLExact (panEntryProgram start)
      (panClockContext context clock) with
  | some pair => (pair.1, pair.2.state)
  | none => (none, { context.state with clock := clock })

/-- The FFI event list of a clock-indexed evaluation result, i.e.
`(SND (evaluate (prog, s with clock := k))).ffi.io_events`. -/
def panExactResultEvents {width : Nat} {σ : Type} [NeZero width]
    (pair : Option (PanSemResultExact width) × PanSemStateExact width σ) :
    List HolIoEvent :=
  pair.2.ffi.ioEvents

/-- HOL `semantics_def`'s successful-result outcome mapping:
`SOME (Return _) => Success`, `SOME (FinalFFI e) => FFI_outcome e`, else none. -/
def panExactResultOutcome {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → Option PanSemExactOutcome
  | some (.returned _) => some .success
  | some (.finalFfi event) => some (.ffi event.outcome)
  | _ => none

/-- HOL `semantics_def`'s forbidden-result predicate: `False` for
`SOME TimeOut`/`SOME (FinalFFI _)`/`SOME (Return _)`, `True` otherwise. -/
def panExactForbiddenResult {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → Prop
  | some .timeOut => False
  | some (.finalFfi _) => False
  | some (.returned _) => False
  | _ => True

/-- `∃k.` the clock-`k` entry evaluation yields a forbidden result. -/
def panExactHasForbiddenRun {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) : Prop :=
  ∃ clock, panExactForbiddenResult (panEvaluateClock context start clock).1

/-- `∃k t r outcome.` the clock-`k` entry evaluation yields a successful
`Return`/`FinalFFI` observation. -/
def panExactHasSuccessfulRun {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) : Prop :=
  ∃ (clock : Nat) (result : Option (PanSemResultExact width))
    (final : PanSemStateExact width σ),
    panEvaluateClock context start clock = (result, final) ∧
      (panExactResultOutcome result).isSome = true

/-- HOL `semantics_def`'s `some res` witness selection: pick a successful run
and return `Terminate outcome (event list)`. -/
noncomputable def panExactChooseTermination {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS)
    (witness : panExactHasSuccessfulRun context start) : PanSemExactBehaviour :=
  let clock := Classical.choose witness
  let hrest := Classical.choose_spec witness
  let hrest2 := Classical.choose_spec hrest
  let hsome := (Classical.choose_spec hrest2).2
  .terminate (Classical.choose (Option.isSome_iff_exists.mp hsome))
    (panExactResultEvents (panEvaluateClock context start clock))

/-- HOL `semantics_def` with an explicit divergence LUB (the LUB is
`build_lprefix_lub (IMAGE (fromList ∘ SND ∘ evaluate) UNIV)` in HOL). -/
noncomputable def panSemanticsExactWithLub {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS)
    (divergenceLub : PanLprefixLub
      (fun clock => panExactResultEvents (panEvaluateClock context start clock))) :
    PanSemExactBehaviour := by
  classical
  exact if forbidden : panExactHasForbiddenRun context start then
    .fail
  else if successful : panExactHasSuccessfulRun context start then
    panExactChooseTermination context start successful
  else
    .diverge _ divergenceLub

/-- Flapjack-specific bridge lemma (no direct HOL declaration): the event family
    of `panEvaluateClock` agrees with the additive-clock family of the recursive
    evaluator started from the clock-0 context.  It lets the chain lemma apply
    to the absolute `s with clock := k` family used by HOL `semantics_def`; the
    state and LUB carrier differences in the module note still apply. -/
theorem panExactResultEvents_panEvaluateClock {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) (clock : Nat) :
    panExactResultEvents (panEvaluateClock context start clock) =
      ((evalPanSemRecursiveCallContextHOLExact (panEntryProgram start)
          (ctxAddClock (panClockContext context 0) clock)).map
        (fun result => result.2.state.ffi.ioEvents)).getD [] := by
  have hstate : (panClockContext context clock).state =
      (ctxAddClock (panClockContext context 0) clock).state := by
    simp only [panClockContext, PanSemExactEvalContext.withState_state,
      stateAddClock, Nat.zero_add]
  have heval := eval_context_state (panEntryProgram start) (panClockContext context clock)
    (ctxAddClock (panClockContext context 0) clock) hstate
  unfold panEvaluateClock panExactResultEvents
  rw [heval]
  cases h : evalPanSemRecursiveCallContextHOLExact (panEntryProgram start)
      (ctxAddClock (panClockContext context 0) clock) with
  | none =>
      obtain ⟨o, ho⟩ := evalPanSemRecursiveCallContextHOLExact_total (panEntryProgram start)
        (ctxAddClock (panClockContext context 0) clock)
      rw [h] at ho
      exact absurd ho (by simp)
  | some pair => simp

/-- Flapjack-specific bridge lemma (no direct HOL declaration): the clock-indexed
    event traces used by this semantics construction form a pairwise prefix
    chain, with no caller-supplied hypothesis.  It discharges the internal
    `divergenceChain` argument using evaluator clock monotonicity; it does not
    identify `PanLprefixLub` with HOL `build_lprefix_lub`. -/
theorem panEvaluateClock_ioEvents_lprefixChain {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) :
    panLprefixChain
      (fun clock => panExactResultEvents (panEvaluateClock context start clock)) := by
  simpa only [panExactResultEvents_panEvaluateClock context start] using
    evalPanSemRecursiveCallContextHOLExact_clock_ioEvents_lprefixChain
      (panEntryProgram start) (panClockContext context 0)

/-- Flapjack-specific variant of HOL `panSem$semantics_def` with an explicit
    `PanLprefixLub` witness.  The total wrapper below derives the chain proof;
    this variant is not identified with HOL's `build_lprefix_lub`. -/
noncomputable def panSemanticsExact {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS)
    (divergenceChain : panLprefixChain
      (fun clock => panExactResultEvents (panEvaluateClock context start clock))) :
    PanSemExactBehaviour :=
  panSemanticsExactWithLub context start
    (buildPanLprefixLub _ divergenceChain)

/-- Flapjack-specific observational composition for HOL `panSem$semantics_def`.
    It derives the prefix-chain argument internally, but still uses
    `PanSemStateExact` with unrestricted map fields and `PanLprefixLub`; neither
    carrier is identified here with HOL's finite-map state and
    `build_lprefix_lub`.  See the module note; no `@[hol]` tag is valid. -/
noncomputable def panSemanticsExactTotal {width : Nat} {σ : Type} [NeZero width]
    (context : PanSemExactEvalContext width σ) (start : MlS) : PanSemExactBehaviour :=
  panSemanticsExact context start (panEvaluateClock_ioEvents_lprefixChain context start)

end Flapjack
