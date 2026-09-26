/-
FINITE-SUPPORT CARRIER PROGRAM EVALUATION (flapjack-6yq / flapjack-qj5).

The exact `evaluate_def` evaluator `evalPanSemRecursiveCallContextHOLExact`
(`TotalEvalExact.lean`) quantifies over `PanSemStateExact`, whose
`locals`/`globals`/`code`/`eshapes` are unrestricted `MlS → Option _` functions.
HOL `panSem$state` instead keeps those fields as finite maps (`varname |-> 'a v`,
`|->`), so the evaluator is faithful only on the finite-support subcarrier.

`PanSemStateFiniteExact.evaluateHOLFinite` (in the carrier module
`StateExactFiniteMap.lean`) is the provisional state-level projection of the
direct, clause-for-clause finite context evaluator
`evalPanSemRecursiveCallFiniteContext`.  It currently keeps the outer `Option`
assembly marker (the marker is always `some` once totality is proved; bead
`flapjack-6yq`), so a clause returns `some (result, state)` rather than HOL
`evaluate_def`'s bare `result option × state` pair.  The finite
context threads `memaddrsDecidable`/`shMemaddrsDecidable` (bead `flapjack-6yq`)
so the recursive clauses typecheck over literal record updates.

This module exposes the clause surface of `evaluateHOLFinite`, clause by clause,
as the source evidence for the `evaluate_def` port.  Exposed so far:
`Skip` / `Break` / `Continue`.  The remaining clauses are being added; the
exact `@[hol ... "evaluate_def" ...]` tag stays withheld until every clause is
exposed and reviewed (`flapjack-qj5` is blocked on `flapjack-6yq`).

The older delegating adapter `evaluateHOLFiniteViaExact` (and its
`evalPanSemRecursiveCallHOLFinite_of_broad` / `evaluateHOLFiniteViaExact_of_broad`
translation lemmas) remains as untagged Flapjack-specific infrastructure.
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

/-- Generic translation for the finite adapter: given the broad exact
    evaluator's result on `program`, `evaluateHOLFiniteViaExact` returns the same
    (`result option × state`) pair with the post-state rebuilt through the
    canonical finite-support carrier. -/
theorem evaluateHOLFiniteViaExact_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evaluateHOLFiniteViaExact state program =
      (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  have hw := evalPanSemRecursiveCallHOLFinite_of_broad state program output hb
  unfold evaluateHOLFiniteViaExact
  dsimp only
  rw [hw]

/-- HOL `evaluate_def` `Skip` clause: `evaluate (Skip, s) = (NONE, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.skip : ProgHOL width) = (none, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (none, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Break` clause: `evaluate (Break, s) = (SOME Break, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.break : ProgHOL width) = (some .break, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .break, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Continue` clause: `evaluate (Continue, s) = (SOME Continue, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.continue : ProgHOL width) = (some .continue, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .continue, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Skip` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.skip : ProgHOL width) = some (none, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Break` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.break : ProgHOL width) = some (some .break, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Continue` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.continue : ProgHOL width) = some (some .continue, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

end PanSemStateFiniteExact

end Flapjack
