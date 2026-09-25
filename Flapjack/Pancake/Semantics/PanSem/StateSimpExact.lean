import Flapjack.Pancake.Semantics.PanSem.LocalUpdatesExact
import Flapjack.Pancake.Semantics.PanSem.IsValidValueExact

/-!
# `panSem` state-accessor simplification lemmas over the function-backed carrier

HOL `panSemScript.sml` states three simplification lemmas about the state
accessors, all over the `mlstring`-keyed `varname` maps of the source state:

* `kvar_simps` (`:422-429`):
  `set_kvar Local v value s = set_var v value s`,
  `set_kvar Global v value s = set_global v value s`,
  `lookup_kvar Local v s = FLOOKUP s.locals v`,
  `lookup_kvar Global v s = FLOOKUP s.globals v`.
* `is_valid_value_simps` (`:476-487`): the two clauses of `is_valid_value`
  specialised to `Local`/`Global`, i.e. `is_valid_value s Local v value` is
  `case FLOOKUP s.locals v of SOME w => shape_of value = shape_of w | NONE => F`
  and the `Global` counterpart.
* `is_valid_value_simps2` (`:489-500`): `is_valid_value` and `lookup_kvar` are
  invariant under updating `clock`, `ffi`, `code` or `memory`.

These useful simplification statements use the function-backed
`PanSemStateExact` and its accessor definitions. HOL state maps are finite maps,
while these Lean fields admit arbitrary lookup functions; the theorems are
therefore untagged pending the finite-map carrier prerequisite tracked by
`flapjack-pxn.18.3.7.1.3.1.1.2`. HOL Boolean shape equality is rendered as
`shapeEqHOL`, with bridge `shapeEqHOL_eq_true`.

Direct HOL oracle rows:

* `scripts/hol-probes/pan_sem_e2e_probe.out` — `kvar_simps_set_local`,
  `kvar_simps_lookup_local`, `is_valid_value_clock_update`,
  `is_valid_value_memory_update` (see the additions to
  `scripts/hol-probes/pan_sem_e2e_probeScript.sml`).

They are reproduced by `Flapjack/Test/PanSemStateSimpExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL)

/-- Function-backed rendering of HOL `panSem$kvar_simps` (`panSemScript.sml:422-429`);
    untagged because the state map fields are unrestricted functions rather than
    HOL finite maps. Exact finite-support replacement tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
theorem kvar_simps {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateExact width σ) :
    (setKvarHOLExact .local name value state = setVarHOLExact name value state) ∧
      (setKvarHOLExact .global name value state = setGlobalHOLExact name value state) ∧
      (lookupKvarHOLExact .local name state = state.locals name) ∧
      (lookupKvarHOLExact .global name state = state.globals name) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Function-backed rendering of HOL `panSem$is_valid_value_simps`
    (`panSemScript.sml:476-487`); untagged because the carrier's maps are not
    finite-map fields. Exact finite-support replacement tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
theorem is_valid_value_simps {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (value : ValueHOL width) :
    (isValidValueHOLExact state .local name value =
        (match state.locals name with
          | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
          | none => false)) ∧
      (isValidValueHOLExact state .global name value =
        (match state.globals name with
          | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
          | none => false)) :=
  ⟨rfl, rfl⟩

/-- Function-backed rendering of HOL `panSem$is_valid_value_simps2`
    (`panSemScript.sml:489-500`); untagged because its whole-state binder uses
    function fields in place of HOL finite maps. Exact finite-support
    replacement tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
theorem is_valid_value_simps2 {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (clock : Nat) (ffi : HolFfiState σ)
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (memory : RiscV.Word width → HolWordLab width) :
    (isValidValueHOLExact { state with clock := clock } kind name value =
        isValidValueHOLExact state kind name value) ∧
      (isValidValueHOLExact { state with ffi := ffi } kind name value =
        isValidValueHOLExact state kind name value) ∧
      (isValidValueHOLExact { state with code := code } kind name value =
        isValidValueHOLExact state kind name value) ∧
      (isValidValueHOLExact { state with memory := memory } kind name value =
        isValidValueHOLExact state kind name value) ∧
      (lookupKvarHOLExact kind name { state with clock := clock } =
        lookupKvarHOLExact kind name state) ∧
      (lookupKvarHOLExact kind name { state with ffi := ffi } =
        lookupKvarHOLExact kind name state) ∧
      (lookupKvarHOLExact kind name { state with code := code } =
        lookupKvarHOLExact kind name state) ∧
      (lookupKvarHOLExact kind name { state with memory := memory } =
        lookupKvarHOLExact kind name state) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Flapjack
