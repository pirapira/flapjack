import Flapjack.Pancake.Semantics.PanSem.StateSimpExact

/-!
# `panSem` state-accessor definition bundle over the function-backed carrier

HOL `panSemScript.sml` collects the bodies of the five state-accessor
definitions into a single conjunction:

```
Theorem kvar_defs = LIST_CONJ [set_var_def,set_global_def,set_kvar_def,
                               is_valid_value_def,lookup_kvar_def];
```

`LIST_CONJ` of those definition theorems is exactly the five equations

* `set_var_def` (`:398-401`):
  `set_var v value s = s with locals := s.locals |+ (v,value)`;
* `set_global_def` (`:403-406`): the `globals` counterpart;
* `set_kvar_def` (`:408-413`):
  `set_kvar vk v value s = case vk of Local => set_var v value s
                                        | Global => set_global v value s`;
* `is_valid_value_def` (`:469-475`):
  `is_valid_value s vk v value = case lookup_kvar vk v s of
     SOME w => shape_of value = shape_of w | NONE => F`;
* `lookup_kvar_def` (`:415-420`):
  `lookup_kvar vk v s = case vk of Local => FLOOKUP s.locals v
                                 | Global => FLOOKUP s.globals v`.

The Lean rendering below is the five-way conjunction of those equations over
the `mlstring`-keyed, function-backed `PanSemStateExact`. These equations remain
useful for Lean reduction, but HOL state fields are finite maps and this carrier
admits non-finite-support functions. The theorem is therefore untagged pending
the finite-map carrier prerequisite tracked by
`flapjack-pxn.18.3.7.1.3.1.1.2`. HOL Boolean shape equality is rendered as
`shapeEqHOL`, with bridge `shapeEqHOL_eq_true`.

Scope: this is the conjunction of `Definition`s bundled by `LIST_CONJ`, not a
statement about the recursive evaluator, so it is self-contained over the exact
carrier.  Direct original-HOL rows are in
`scripts/hol-probes/pan_sem_e2e_probe.out` and replayed by
`Flapjack/Test/PanSemStateDefsExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-- Function-backed rendering of HOL `kvar_defs` (`panSemScript.sml:502-503`):
    the five accessor-definition equations as a conjunction; untagged because
    its map fields are unrestricted functions rather than HOL finite maps.
    Exact finite-support replacement tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
theorem kvar_defs {width : Nat} {σ : Type} [NeZero width] :
    (∀ (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ),
        setVarHOLExact name value state =
          { state with locals := fun current =>
              if current = name then some value else state.locals current }) ∧
    (∀ (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ),
        setGlobalHOLExact name value state =
          { state with globals := fun current =>
              if current = name then some value else state.globals current }) ∧
    (∀ (kind : VarKind) (name : MlS) (value : ValueHOL width)
        (state : PanSemStateExact width σ),
        setKvarHOLExact kind name value state =
          match kind with
          | .local => setVarHOLExact name value state
          | .global => setGlobalHOLExact name value state) ∧
    (∀ (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
        (value : ValueHOL width),
        isValidValueHOLExact state kind name value =
          match lookupKvarHOLExact kind name state with
          | some existing =>
              shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
          | none => false) ∧
    (∀ (kind : VarKind) (name : MlS) (state : PanSemStateExact width σ),
        lookupKvarHOLExact kind name state =
          match kind with
          | .local => state.locals name
          | .global => state.globals name) :=
  ⟨fun _ _ _ => rfl,
   fun _ _ _ => rfl,
   fun kind _ _ _ => by cases kind <;> rfl,
   fun _ kind _ _ => by cases kind <;> rfl,
   fun kind _ _ => by cases kind <;> rfl⟩

end Flapjack
