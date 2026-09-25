/-
Copyright (c) 2026 Flapjack contributors.

Exact control flow of HOL `panSem$semantics_decls` over the exact MlString carriers.

`cakeml/pancake/semantics/panSemScript.sml:861-869` defines

```
Definition semantics_decls_def:
  semantics_decls ^s start decls =
  case decs_stcnames [] decls of
  | NONE => Fail
  | SOME st_ctxt =>
    case evaluate_decls (s with structs := st_ctxt) decls of
    | NONE => Fail
    | SOME s' => semantics s' start
End
```

The two sub-computations are already ported exactly and tagged:

* `decs_stcnames` as `decsStcnamesHOLExact`
  (`Flapjack/Pancake/Semantics/PanSem/DeclContextExact.lean`), and
* `evaluate_decls` as `evaluateDeclsHOLExact`
  (`Flapjack/Pancake/Semantics/PanSem/EvaluateDeclsExact.lean`).

The remaining dependency is `semantics_def` (`panSemScript.sml:785-809`): the
observational semantics that quantifies over clock-indexed runs of the recursive
`evaluate` and otherwise returns `build_lprefix_lub` of the FFI-event prefixes,
with the `Terminate`/`Diverge`/`Fail` result. Lean only has the untagged
production-state `Flapjack.PanObservationalSemantics` (`PanBehaviour` over
`PanValueFfiClockResult`), not an exact MlString-carrier port of `semantics_def`.

Therefore `semanticsDeclsHOLExact` below is stated with the HOL control flow but
takes the `Fail` outcome and the final `semantics` call as parameters.  It is
FLAPJACK-SPECIFIC (not a statement-exact HOL port) and deliberately UNTAGGED:
adding the two parameters changes the statement, and no exact `semantics` port
exists yet.  The gap is tracked by child bead
`flapjack-pxn.18.3.6.9.24.1`; the `@[hol semantics_decls_def]` tag may be added
once the exact `semantics_def` port lands and the parameters are instantiated.

The direct original-HOL oracle rows for the two failure branches live in
`scripts/hol-probes/pan_sem_e2e_probe.out`
(`semantics_decls_bad_struct=Fail`, `semantics_decls_bad_function=Fail`,
`semantics_decls_bad_exception=Fail`) and are replayed by
`Flapjack/Test/PanSemSemanticsDeclsExactParity.lean`.
-/

import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS DeclHOL StructContextExact)

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): the exact control flow of
HOL `panSem$semantics_decls` (`cakeml/pancake/semantics/panSemScript.sml:861-869`)
over the exact carriers.

The structure context is computed by `decsStcnamesHOLExact` (HOL `decs_stcnames`),
`none` yields the supplied `failure` outcome (HOL `Fail`), otherwise the
declarations are evaluated by `evaluateDeclsHOLExact` (HOL `evaluate_decls`) under
`structs := structContext`; `none` again yields `failure`, and `some state'` calls
the supplied `runSemantics state' start` (HOL `semantics s' start`).

The `failure`/`runSemantics` parameters stand in for HOL's `Fail`/`semantics`
because the exact `semantics_def` port has not landed yet (see the module
docstring); this is why no `@[hol semantics_decls_def]` tag is attached. -/
def semanticsDeclsHOLExact {width : Nat} {σ : Type} {ω : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (start : MlS) (declarations : List (DeclHOL width))
    (failure : ω) (runSemantics : PanSemStateExact width σ → MlS → ω) : ω :=
  match decsStcnamesHOLExact (width := width) [] declarations with
  | none => failure
  | some structContext =>
      match evaluateDeclsHOLExact { state with structs := structContext } declarations with
      | none => failure
      | some state' => runSemantics state' start

@[simp] theorem semanticsDeclsHOLExact_decs_none {width : Nat} {σ : Type} {ω : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (start : MlS) (declarations : List (DeclHOL width)) (failure : ω)
    (runSemantics : PanSemStateExact width σ → MlS → ω)
    (h : decsStcnamesHOLExact (width := width) [] declarations = none) :
    semanticsDeclsHOLExact state start declarations failure runSemantics = failure := by
  simp only [semanticsDeclsHOLExact, h]

@[simp] theorem semanticsDeclsHOLExact_evaluate_none {width : Nat} {σ : Type} {ω : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (start : MlS) (declarations : List (DeclHOL width)) (failure : ω)
    (runSemantics : PanSemStateExact width σ → MlS → ω)
    (structContext : StructContextExact)
    (hdecs : decsStcnamesHOLExact (width := width) [] declarations = some structContext)
    (heval : evaluateDeclsHOLExact { state with structs := structContext } declarations = none) :
    semanticsDeclsHOLExact state start declarations failure runSemantics = failure := by
  simp only [semanticsDeclsHOLExact, hdecs, heval]

theorem semanticsDeclsHOLExact_ok {width : Nat} {σ : Type} {ω : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (start : MlS) (declarations : List (DeclHOL width)) (failure : ω)
    (runSemantics : PanSemStateExact width σ → MlS → ω)
    (structContext : StructContextExact) (state' : PanSemStateExact width σ)
    (hdecs : decsStcnamesHOLExact (width := width) [] declarations = some structContext)
    (heval : evaluateDeclsHOLExact { state with structs := structContext } declarations = some state') :
    semanticsDeclsHOLExact state start declarations failure runSemantics = runSemantics state' start := by
  simp only [semanticsDeclsHOLExact, hdecs, heval]

end Flapjack
