/-
FINITE-SUPPORT CARRIER PROGRAM EVALUATION (flapjack-qj5).

The exact `evaluate_def` evaluator `evalPanSemRecursiveCallContextHOLExact`
(`TotalEvalExact.lean`) quantifies over `PanSemStateExact`, whose
`locals`/`globals`/`code`/`eshapes` are unrestricted `MlS → Option _` functions.
HOL `panSem$state` instead keeps those fields as finite maps (`varname |-> 'a v`,
`|->`), so the evaluator is faithful only on the finite-support subcarrier.

The tagged wrapper `PanSemStateFiniteExact.evaluateHOLFinite` lives in
`Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean`, the same module as
the carrier `PanSemStateFiniteExact` and the canonical translation witness
`holFmapAsFiniteSupportWitness` (the `fmap_as_finite_support` qualifier requires
the owning structure, the witness, and the tagged declaration to share a module).
Its body extracts the total finite-support recursive evaluator
`evalPanSemRecursiveCallHOLFinite`; because HOL `evaluate_def` is well-founded
recursion, that body delegates rather than syntactically presenting HOL's
clause-shaped body, exactly as the reviewed `evalHOLFinite` does for `eval_def`.

This module provides the clause-shaped equations that expose the `evaluate_def`
clauses over the finite carrier.  `evaluateHOLFinite_of_broad` and
`evalPanSemRecursiveCallHOLFinite_of_broad` are the generic translation lemmas
that relate the finite wrapper to the broad exact evaluator for any program and
any broad result; the per-constructor equations below specialise them to the
`Skip` / `Break` / `Continue` clauses.  They are the per-clause review surface
cited by the tagged definition.
-/
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL)

namespace PanSemStateFiniteExact

/-- Generic translation: given the broad exact evaluator's result on `program`,
    the finite recursive evaluator returns the same result with the post-state
    rebuilt through the canonical finite-support carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evalPanSemRecursiveCallHOLFinite state program =
      some (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  rw [evalPanSemRecursiveCallHOLFinite.eq_def]
  dsimp only
  split
  · rename_i hres
    rw [hb] at hres
    simp at hres
  · rename_i pair hres
    rw [hb] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    rfl

/-- Generic translation for the tagged finite evaluator: given the broad exact
    evaluator's result on `program`, `evaluateHOLFinite` returns the same
    (`result option × state`) pair with the post-state rebuilt through the
    canonical finite-support carrier. -/
theorem evaluateHOLFinite_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evaluateHOLFinite state program =
      (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  have hw := evalPanSemRecursiveCallHOLFinite_of_broad state program output hb
  unfold evaluateHOLFinite
  dsimp only
  rw [hw]

/-- HOL `evaluate_def` `Skip` clause: `evaluate (Skip, s) = (NONE, s)`. -/
@[simp] theorem evaluateHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.skip : ProgHOL width) = (none, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (none, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFinite_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Break` clause: `evaluate (Break, s) = (SOME Break, s)`. -/
@[simp] theorem evaluateHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.break : ProgHOL width) = (some .break, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .break, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFinite_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Continue` clause: `evaluate (Continue, s) = (SOME Continue, s)`. -/
@[simp] theorem evaluateHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.continue : ProgHOL width) = (some .continue, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .continue, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFinite_of_broad state _ _ hb]
  simp only [ofExact_toExact]

end PanSemStateFiniteExact

end Flapjack
