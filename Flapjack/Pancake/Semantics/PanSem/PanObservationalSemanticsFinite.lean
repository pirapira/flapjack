import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.PanObservationalSemantics

/-!
Finite-map-carrier clock observations for `panSem$semantics_def`.

This module supplies clock-indexed observations on the canonical finite-map
state while retaining the legacy witness-carrying behaviour API. The tagged
full original `semantics` and `semanticsDecls` definitions, with HolBehaviour
results, are in the sibling `Semantics.lean`. This support API does not itself
identify those result carriers or establish the executed production route.

The main observational construction currently uses the broad exact state whose
map fields are unrestricted functions. This module exposes the same clocked
entry call over `PanSemStateFiniteExact` and proves its projection to that
broad observation. It is Flapjack-specific support: the divergence LUB still
uses `PanLprefixLub`, which has no reviewed correspondence to HOL's generic
`build_lprefix_lub`/`llist` choice boundary; see bead `flapjack-4ac.4.105.2`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-- The finite-map state viewed by the broad exact evaluator, with classical
    decisions for HOL's predicate-valued address domains discharged locally.
    No decidability argument is exposed in the public clocked observation. -/
noncomputable def panSemExactContextOfFiniteState {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) :
    PanSemExactEvalContext width σ := by
  classical
  exact ⟨state.toExact, inferInstance, inferInstance⟩

/-- The clock-`k` result/post-state for the entry call `Call NONE start []`,
    evaluated directly over the reviewed finite-support source state. -/
noncomputable def panEvaluateClockFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat) :
    Option (PanSemResultExact width) × PanSemStateFiniteExact width σ := by
  classical
  let clockState : PanSemStateFiniteExact width σ := { state with clock := clock }
  exact Classical.choose
    (PanSemStateFiniteExact.evalPanSemRecursiveCallHOLFinite_exists
      clockState (panEntryProgram start))

/-- The finite recursive evaluator is total, so `panEvaluateClockFinite` is
    its unique result/post-state pair. -/
theorem panEvaluateClockFinite_spec {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat) : by
  classical
  exact
    PanSemStateFiniteExact.evalPanSemRecursiveCallHOLFinite
      ({ state with clock := clock })
      (panEntryProgram start) = some (panEvaluateClockFinite state start clock)
  := by
  classical
  exact Classical.choose_spec
    (PanSemStateFiniteExact.evalPanSemRecursiveCallHOLFinite_exists
      ({ state with clock := clock }) (panEntryProgram start))

/-- The direct finite-state clock observation projects to the existing broad
    exact `panEvaluateClock` observation. This isolates the state/map-carrier
    translation; it does not establish a translation for the divergence LUB. -/
theorem panEvaluateClockFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat) :
    ((panEvaluateClockFinite state start clock).1,
      (panEvaluateClockFinite state start clock).2.toExact) =
      panEvaluateClock (panSemExactContextOfFiniteState state) start clock := by
  classical
  let finiteState : PanSemStateFiniteExact width σ := { state with clock := clock }
  have hfinite := panEvaluateClockFinite_spec state start clock
  have hprojection := PanSemStateFiniteExact.evalPanSemRecursiveCallHOLFinite_toExact
    finiteState (panEntryProgram start)
  rw [hfinite] at hprojection
  simp only [Option.map_some] at hprojection
  let broadContext := panSemExactContextOfFiniteState state
  let finiteContext := panSemExactContextOfFiniteState finiteState
  have hstate : finiteContext.state = (panClockContext broadContext clock).state := by
    rfl
  have heval := eval_context_state (panEntryProgram start) finiteContext
    (panClockContext broadContext clock) hstate
  change some ((panEvaluateClockFinite state start clock).1,
      (panEvaluateClockFinite state start clock).2.toExact) =
    (evalPanSemRecursiveCallContextHOLExact (panEntryProgram start) finiteContext).map
      (fun pair => (pair.1, pair.2.state)) at hprojection
  rw [heval] at hprojection
  cases hbroad : evalPanSemRecursiveCallContextHOLExact (panEntryProgram start)
      (panClockContext broadContext clock) with
  | none => simp [hbroad] at hprojection
  | some pair =>
      simp only [hbroad, Option.map_some] at hprojection
      have hpairs := Option.some.inj hprojection
      have hpairs' : (panEvaluateClockFinite state start clock).1 = pair.1 ∧
          (panEvaluateClockFinite state start clock).2.toExact = pair.2.state := by
        exact Prod.mk.inj hpairs
      unfold panEvaluateClock
      rw [hbroad]
      exact Prod.ext hpairs'.1 hpairs'.2

end Flapjack
