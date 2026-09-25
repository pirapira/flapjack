/-
FINITE-SUPPORT CARRIER EVALUATION (flapjack-pxn.18.3.7.1.3.1.1.2.5).

The exact `eval_def` evaluator `evalHOLExact` (`EvalExact.lean`) quantifies over
`PanSemStateExact`, whose `locals`/`globals`/`code`/`eshapes` are unrestricted
`MlS → Option _` functions.  HOL `panSem$state` instead keeps those fields as
finite maps (`varname |-> 'a v`, `|->`), so the evaluator is faithful only on the
finite-support subcarrier.

This module wraps the reviewed evaluator so its state quantification is
`PanSemStateFiniteExact`, whose four map fields are `HolFiniteMapExact`
(finite support by type).  The wrappers delegate through
`PanSemStateFiniteExact.toExact`, so all fifteen `eval_def` clauses and the mutual
`OPT_MMAP` / structured-field helpers of `EvalExact.lean` are reused unchanged;
the projection equalities below are definitional.

No `@[hol]` tag: a clause-shaped rendering over the finite carrier plus the
`fmap_as_finite_support` qualifier, per-clause source review, and type-lock
coverage are tracked by the parent bead `flapjack-pxn.18.3.7.1.3.1.1.2.5`.
-/
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL MlS)

namespace PanSemStateFiniteExact

/-- Finite-support carrier rendering of HOL `eval` (`panSemScript.sml:209-283`):
    delegate the broad evaluator through the projection `toExact`. -/
def evalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  evalHOLExact state.toExact

/-- Finite-support carrier rendering of the `OPT_MMAP eval` list step. -/
def evalListHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  evalListHOLExact state.toExact

/-- Finite-support carrier rendering of the named-struct field-expression step. -/
def evalListFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs] :
    List (MlS × ExpHOL width) → Option (List (MlS × ValueHOL width)) :=
  evalListFieldsHOLExact state.toExact

@[simp] theorem evalHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs]
    (expression : ExpHOL width) :
    state.evalHOLFinite expression = evalHOLExact state.toExact expression := rfl

@[simp] theorem evalListHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs]
    (expressions : List (ExpHOL width)) :
    state.evalListHOLFinite expressions = evalListHOLExact state.toExact expressions := rfl

@[simp] theorem evalListFieldsHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.toExact.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    state.evalListFieldsHOLFinite fields = evalListFieldsHOLExact state.toExact fields := rfl

end PanSemStateFiniteExact

end Flapjack
