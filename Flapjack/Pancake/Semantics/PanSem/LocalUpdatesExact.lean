import Flapjack.Pancake.Semantics.PanSem.StateExact

/-!
# Exact `panSem` local/global update helpers over the exact carrier

HOL `panSemScript.sml` provides four small state-update helpers that update the
`varname`-keyed (`mlstring`) local/global finite maps:

* `set_var_def` (`:398-401`): `set_var v value s = s with locals := s.locals |+ (v,value)`
* `set_global_def` (`:403-406`): the same on `globals`
* `upd_locals_def` (`:431-434`): `upd_locals varargs s = s with locals := FEMPTY |++ varargs`
* `res_var_def` (`:505-508`):
  `res_var lc (n, NONE) = lc \\ n` and `res_var lc (n, SOME v) = lc |+ (n,v)`

The state carrier here is the exact `PanSemStateExact` (`StateExact.lean`), whose
`locals`/`globals` are `MlS → Option (ValueHOL width)` maps.  HOL `|+`/`|++`/`\\`
are `=`-keyed finite-map operations; rendering them as `=`-keyed function
updates over `MlS` (which has decidable equality) matches HOL, including
`|++`'s "later duplicate wins" behaviour
(`finite_mapsTheory.FLOOKUP_FUPDATE_LIST`: `FLOOKUP (m |++ xs) k` uses
`ALOOKUP (REVERSE xs) k`).

Direct HOL oracle rows:

* `scripts/hol-probes/pan_sem_set_var_probe.out` —
  `set_var_new`, `set_var_overwrite`, `set_var_other`, `set_var_globals`,
  `set_var_clock`, `set_global_new`, `set_global_locals`, `upd_locals_x`,
  `upd_locals_other`, `upd_locals_dup`
* `scripts/hol-probes/pan_res_var_probe.out` —
  `delete_hit`, `delete_other`, `update_hit`

They are reproduced by `Flapjack/Test/PanSemLocalUpdatesExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS)

/-- Exact port of HOL `panSem$set_var` (`panSemScript.sml:398-401`):
    `set_var v value s = s with locals := s.locals |+ (v,value)`.  `|+` is
    `FUPDATE`, rendered over the `MlS`-keyed function map with `=`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"]
def setVarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    locals := fun current => if current = name then some value else state.locals current }

/-- Exact port of HOL `panSem$set_global` (`panSemScript.sml:403-406`): the
    `globals` counterpart of `set_var`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_global_def"]
def setGlobalHOLExact {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    globals := fun current => if current = name then some value else state.globals current }

/-- Exact port of HOL `panSem$upd_locals` (`panSemScript.sml:431-434`):
    `upd_locals varargs s = s with locals := FEMPTY |++ varargs`.  `|++` is
    `FUPDATE_LIST`; the `List.foldl` over the function map applies entries left
    to right, so a later duplicate overrides an earlier one, and any binding not
    mentioned is dropped (starting from `FEMPTY`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "upd_locals_def"]
def updLocalsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (varargs : List (MlS × ValueHOL width))
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    locals := List.foldl
      (fun (map : MlS → Option (ValueHOL width)) (entry : MlS × ValueHOL width) =>
        fun current => if current = entry.1 then some entry.2 else map current)
      (fun _ => none) varargs }

/-- Exact port of HOL `panSem$res_var` (`panSemScript.sml:505-508`):
    `res_var lc (n, NONE) = lc \\ n` and `res_var lc (n, SOME v) = lc |+ (n,v)`.
    Rendered over a `MlS`-keyed function map: `NONE` deletes the binding
    (`FDOMSUB`), `SOME v` updates it (`FUPDATE`), both with `=`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "res_var_def"]
def resVarHOLExact {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (entry : MlS × Option (ValueHOL width)) : MlS → Option (ValueHOL width) :=
  match entry.2 with
  | none => fun current => if current = entry.1 then none else locals current
  | some value => fun current => if current = entry.1 then some value else locals current

end Flapjack
