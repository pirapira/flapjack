import Flapjack.Pancake.Semantics.PanSem.StateExact

/-!
# `panSem` local/global update helpers over the function-backed carrier

HOL `panSemScript.sml` provides four small state-update helpers that update the
`varname`-keyed (`mlstring`) local/global finite maps:

* `set_var_def` (`:398-401`): `set_var v value s = s with locals := s.locals |+ (v,value)`
* `set_global_def` (`:403-406`): the same on `globals`
* `upd_locals_def` (`:431-434`): `upd_locals varargs s = s with locals := FEMPTY |++ varargs`
* `res_var_def` (`:505-508`):
  `res_var lc (n, NONE) = lc \\ n` and `res_var lc (n, SOME v) = lc |+ (n,v)`

These definitions are useful function-backed renderings over
`PanSemStateExact` (`StateExact.lean`), whose `locals`/`globals` are unrestricted
`MlS → Option (ValueHOL width)` functions. HOL `|+`/`|++`/`\\` operate on
finite maps. Although the pointwise update behavior agrees on represented
finite maps (including `|++`'s later-duplicate-wins behavior), these declarations
quantify over arbitrary functions and therefore are not exact HOL ports. Their
`@[hol]` tags are withheld pending a state carrier whose fields enforce finite
support.

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

/-- Function-backed analogue of HOL `panSem$set_var` (`panSemScript.sml:398-401`).
    This retains pointwise FUPDATE behavior, but is untagged: the state admits
    arbitrary `MlS → Option _` fields rather than HOL finite maps. -/
def setVarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    locals := fun current => if current = name then some value else state.locals current }

/-- Function-backed analogue of HOL `panSem$set_global` (`panSemScript.sml:403-406`);
    untagged because the state carrier admits non-finite-support maps. -/
def setGlobalHOLExact {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    globals := fun current => if current = name then some value else state.globals current }

/-- Function-backed analogue of HOL `panSem$upd_locals` (`panSemScript.sml:431-434`).
    It models FEMPTY followed by FUPDATE_LIST pointwise, but is untagged because
    its state type is not restricted to finite maps. Exact finite-support
    replacement tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.5` (parent `.2.3`). -/
def updLocalsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (varargs : List (MlS × ValueHOL width))
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with
    locals := List.foldl
      (fun (map : MlS → Option (ValueHOL width)) (entry : MlS × ValueHOL width) =>
        fun current => if current = entry.1 then some entry.2 else map current)
      (fun _ => none) varargs }

/-- Function-backed analogue of HOL `panSem$res_var` (`panSemScript.sml:505-508`).
    Its delete/update behavior is pointwise, but its function-map input is not
    the finite-map carrier quantified by HOL, so it is untagged. Exact
    finite-support replacement tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.5`
    (parent `.2.3`). -/
def resVarHOLExact {width : Nat} [NeZero width]
    (locals : MlS → Option (ValueHOL width))
    (entry : MlS × Option (ValueHOL width)) : MlS → Option (ValueHOL width) :=
  match entry.2 with
  | none => fun current => if current = entry.1 then none else locals current
  | some value => fun current => if current = entry.1 then some value else locals current

end Flapjack
