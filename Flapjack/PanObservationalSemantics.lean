import Flapjack.Pancake.Semantics.PanSem
import Flapjack.LoopObservationalSemantics

/-!
# Pancake `panSem.semantics`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:785-809`
(`semantics_def`).  The source repeatedly evaluates
`Call NONE start []` at clock-indexed states, fails when a run is neither a
timeout/final-FFI/return observation nor a permitted residual run, chooses a
successful `Return` or `FinalFFI` witness, and otherwise returns the
`build_lprefix_lub` of the clock-indexed FFI-event prefixes.

The prefix-LUB relation is shared with the already source-shaped loop
semantics port; the aliases below keep the Pancake boundary source-named
without introducing a second divergent LUB proof.

-- FLAPJACK-SPECIFIC (not an exact port of HOL `panSem$semantics_def` or
-- `panSem$semantics_decls_def`): `panSemantics` takes an arbitrary evaluator
-- hook and a caller-provided proof of the event-prefix chain, whereas HOL
-- quantifies the source state and start name, runs its total `evaluate` at
-- every clock, and constructs the divergence LUB from those executions.
-- `semantics_decls` additionally composes the fresh `decs_stcnames` context,
-- `evaluate_decls`, and that exact source semantics. The individual exact
-- finite-map declaration helpers exist, but this faithful composition waits
-- on the total finite-map evaluator and event-chain proof tracked by
-- `flapjack-pxn.18.4.3.77.17` (blocked by `.77.2`).
-/

namespace Flapjack

abbrev PanLList (α : Type u) := LoopLList α
abbrev PanLprefixLubPredicate (family : Nat → List α) (trace : PanLList α) : Prop :=
  LoopLprefixLubPredicate family trace
abbrev PanLprefixLub (family : Nat → List α) := LoopLprefixLub family
abbrev panLprefixChain (family : Nat → List α) : Prop := loopLprefixChain family

noncomputable def buildPanLprefixLub (family : Nat → List α)
    (chain : panLprefixChain family) : PanLprefixLub family :=
  buildLoopLprefixLub family chain

inductive PanSemanticOutcome where
  | success
  | ffi (outcome : FfiOutcome)
  deriving DecidableEq, Repr

inductive PanBehaviour where
  | diverge (family : Nat → List FfiEvent)
      (trace : PanLprefixLub family)
  | terminate (outcome : PanSemanticOutcome) (events : List FfiEvent)
  | fail

structure PanSemanticsHooks (α : Type u) (σ : Type v) where
  evaluate : Nat → Option (PanValueFfiClockResult α σ)
  ffiOutcome : FfiFinalEvent → FfiOutcome

def panResultFfi : PanValueFfiClockResult α σ → FfiState σ
  | (.control (.normal _ _ _ ffi), _) => ffi
  | (.control (.returned _ _ _ ffi _), _) => ffi
  | (.control (.raised _ _ _ ffi _ _), _) => ffi
  | (.control (.broke _ _ _ ffi), _) => ffi
  | (.control (.continued _ _ _ ffi), _) => ffi
  | (.control (.finalFfi _ _ _ ffi _), _) => ffi
  | (.control (.error _ _ _ ffi), _) => ffi
  | (.timeout _ _ _ ffi, _) => ffi

def panResultEvents : Option (PanValueFfiClockResult α σ) → List FfiEvent
  | some result => (panResultFfi result).ioEvents
  | none => []

def panResultOutcome (hooks : PanSemanticsHooks α σ)
    (result : Option (PanValueFfiClockResult α σ)) :
    Option PanSemanticOutcome :=
  match result with
  | some (.control (.returned _ _ _ _ _), _) => some .success
  | some (.control (.finalFfi _ _ _ _ event), _) =>
      some (.ffi (hooks.ffiOutcome event))
  | _ => none

def panForbiddenResult : Option (PanValueFfiClockResult α σ) → Prop
  | some (.timeout _ _ _ _, _) => False
  | some (.control (.finalFfi _ _ _ _ _), _) => False
  | some (.control (.returned _ _ _ _ _), _) => False
  | _ => True

def panHasForbiddenRun (hooks : PanSemanticsHooks α σ) : Prop :=
  ∃ clock, panForbiddenResult (hooks.evaluate clock)

def panHasSuccessfulRun (hooks : PanSemanticsHooks α σ) : Prop :=
  ∃ clock result outcome,
    hooks.evaluate clock = some result ∧
      panResultOutcome hooks (some result) = some outcome

noncomputable def panChooseTermination (hooks : PanSemanticsHooks α σ)
    (witness : panHasSuccessfulRun hooks) : PanBehaviour :=
  let _clock := Classical.choose witness
  let resultWitness := Classical.choose_spec witness
  let result := Classical.choose resultWitness
  let outcomeWitness := Classical.choose_spec resultWitness
  let outcome := Classical.choose outcomeWitness
  .terminate outcome (panResultEvents (some result))

noncomputable def panSemanticsWithLub (hooks : PanSemanticsHooks α σ)
    (divergenceLub : PanLprefixLub
      (fun clock => panResultEvents (hooks.evaluate clock))) : PanBehaviour :=
  by
    classical
    exact if forbidden : panHasForbiddenRun hooks then
      .fail
    else if successful : panHasSuccessfulRun hooks then
      panChooseTermination hooks successful
    else
      .diverge _ divergenceLub

/-! This specialized API is not HOL
`panProps$semantics_wrapper_def` (`cakeml/pancake/semantics/panPropsScript.sml:1824`).
HOL accepts an arbitrary function `f : Nat → semantics_run_res × events`, with
the three result cases `RunError`, `CompleteResult`, and `Incomplete`, and
constructs the divergence LUB from `IMAGE (fromList ∘ SND ∘ f) UNIV`. This Lean
API instead accepts only `PanSemanticsHooks.evaluate : Nat → Option
PanValueFfiClockResult` and requires a proof-carrying `PanLprefixLub` as an
argument. The restricted result carrier and caller-supplied LUB both change
the definition's quantified type/body. No HOL tag is claimed; the faithful
generic wrapper and LUB carrier are tracked by `flapjack-4ac.4.105.1`.

This hook-parameterized definition is also not HOL
`panProps$evaluate_io_events_lprefix_chain`
(`cakeml/pancake/semantics/panPropsScript.sml:1784`). That theorem proves the
clock-indexed event family of the exact `evaluate (p, s with clock := k)` is an
`lprefix_chain`, using `evaluate_add_clock_io_events_mono`; it does not assume
the chain. This definition instead requires `divergenceChain` as an input and
its `PanSemanticsHooks.evaluate` may be any clock-to-result function. The
faithful evaluator-derived chain proof is tracked by
`flapjack-4ac.3.52.3` (which depends on the finite-support evaluator
`flapjack-4ac.3.52.1`). Do not tag this definition as the HOL theorem. -/
noncomputable def panSemantics (hooks : PanSemanticsHooks α σ)
    (divergenceChain : panLprefixChain
      (fun clock => panResultEvents (hooks.evaluate clock))) : PanBehaviour :=
  panSemanticsWithLub hooks
    (buildPanLprefixLub _ divergenceChain)

end Flapjack
