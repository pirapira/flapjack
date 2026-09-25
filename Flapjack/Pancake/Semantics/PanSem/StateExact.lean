import Flapjack.HolRef
import Flapjack.FfiHOL
import Flapjack.RiscV.Model
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# `panSem$state` projection over the faithful `mlstring` name carrier

HOL `panSem$state` (`cakeml/pancake/semantics/panSemScript.sml:44-62`) is

```
<'a, 'ffi> state = <|
  locals    : varname |-> 'a v;
  globals   : varname |-> 'a v;
  structs   : (stcname # struct_info) list;
  code      : funname |-> ((varname # shape) list # 'a prog # shape);
  eshapes   : eid |-> shape;
  memory    : 'a word -> 'a word_lab;
  memaddrs  : ('a word) set;
  sh_memaddrs : ('a word) set;
  clock     : num;
  be        : bool;
  ffi       : 'ffi ffi_state;
  base_addr : 'a word;
  top_addr  : 'a word
|>
```

where `varname`, `stcname`, `fldname`, `funname`, `eid` are all `mlstring`
(`panLangScript.sml:23-25`) and `'a v` is the three-constructor value whose
`Val` wraps `'a word_lab` (`panSemScript.sml:17-26`).

`Flapjack.PanSemHolState` (`PanSemStateEval.lean`) is the String-backed source
projection used by the executed evaluator; its `dec_clock_def`/`fix_clock_def`
and `lookup_kvar_def`/`set_kvar_def` tags are withheld under the
String/MlString carrier rule (`flapjack-0lj`). This module introduces
`PanSemStateExact` over `MlS` keys, `ShapeHOL`/`StructContextExact` syntax,
`ProgHOL` code and the `ValueHOL` value carrier. Its map-valued fields are
currently unrestricted lookup functions, however, so it is a function-backed
projection rather than the HOL finite-map state carrier. State operations and
the declarations that depend on them remain useful Lean infrastructure, but
their `@[hol]` tags were withdrawn by audit bead
`flapjack-pxn.18.3.7.1.3.1.2`; restoration depends on the finite-map carrier
replacement tracked by open bead `flapjack-pxn.18.3.7.1.3.1.1.2`.

Direct HOL oracle rows for the helpers live in
`scripts/hol-probes/pan_sem_e2e_probe.out` (`dec_clock_step`,
`fix_clock_clamps`, `fix_clock_keeps_new`, `lookup_kvar_local`,
`lookup_kvar_global`, `lookup_kvar_missing`); they are reproduced by
`Flapjack/Test/PanSemStateExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ProgHOL)

/-- Exact `panSem$state` over the faithful `mlstring` carrier.

    Field types follow HOL: `locals`/`globals` are `varname`-keyed (here `MlS`)
    `'a v` maps, `structs` is the `mlstring`-named struct context, `code` maps a
    `funname` to its parameter list, body `prog` and return shape, `eshapes` maps
    an exception identifier to a shape, `memory` is a total `'a word -> 'a
    word_lab` map, `memaddrs`/`sh_memaddrs` are word sets (here `Prop` with
    decidability supplied at use sites), `ffi` is the exact HOL `'ffi ffi_state`
    carrier (`Flapjack.HolFfiState σ`), and `base_addr`/`top_addr` are words.
    The positive-width constraint mirrors HOL's positive `dimindex`, matching the
    `ProgHOL`/`ValueHOL` carriers. -/
structure PanSemStateExact (width : Nat) (σ : Type) [NeZero width] where
  locals : MlS → Option (ValueHOL width)
  globals : MlS → Option (ValueHOL width)
  structs : StructContextExact
  code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  eshapes : MlS → Option ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port). HOL `panSem$dec_clock`
    (`panSemScript.sml:441`) is `dec_clock s = s with clock := s.clock - 1` over
    the HOL finite-map state, but `PanSemStateExact` stores `locals`/`globals`/
    `code`/`eshapes` as unrestricted lookup functions `MlS → Option _`, a strict
    superset of HOL finite maps (infinite-support lookups are admitted). The
    equation is faithful only on the finite-support subcarrier
    (`PanSemStateExact.FiniteSupport`, preserved by
    `PanSemStateExact.finiteSupport_decClock` in `StateExactFinite.lean`). The
    exact finite-map carrier rebuild and tag restoration is tracked by bead
    `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def decClockHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with clock := state.clock - 1 }

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port). HOL `panSem$fix_clock`
    (`panSemScript.sml:446`) is over the HOL finite-map state; the equation below
    is faithful only on `PanSemStateExact.FiniteSupport` (preserved by
    `PanSemStateExact.finiteSupport_fixClock` in `StateExactFinite.lean`), while
    `PanSemStateExact`'s unrestricted `MlS → Option _` fields admit non-HOL
    states. Exact finite-map carrier rebuild and tag restoration tracked by bead
    `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def fixClockHOLExact {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateExact width σ) (step : β × PanSemStateExact width σ) :
    β × PanSemStateExact width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port). HOL `panSem$lookup_kvar`
    (`panSemScript.sml:415`) reads the HOL finite-map state; the read below is
    faithful only on `PanSemStateExact.FiniteSupport`, since the unrestricted
    `MlS → Option _` carrier admits non-HOL states. Exact finite-map carrier
    rebuild and tag restoration tracked by bead
    `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def lookupKvarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateExact width σ) :
    Option (ValueHOL width) :=
  match kind with
  | .local => state.locals name
  | .global => state.globals name

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port). HOL `panSem$set_kvar`
    (`panSemScript.sml:408-412`) updates the HOL finite-map state via `|+`
    (counterpart `FUPDATE`, which is `=`-based); the update below is faithful
    only on `PanSemStateExact.FiniteSupport` (preserved by
    `PanSemStateExact.finiteSupport_setKvar` in `StateExactFinite.lean`), since
    the unrestricted `MlS → Option _` carrier admits non-HOL states. Exact
    finite-map carrier rebuild and tag restoration tracked by bead
    `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def setKvarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  match kind with
  | .local =>
      { state with locals := fun current => if current = name then some value else state.locals current }
  | .global =>
      { state with globals := fun current => if current = name then some value else state.globals current }

/- FLAPJACK-SPECIFIC (not a statement-exact HOL port). HOL `panSem$empty_locals`
    (`panSemScript.sml:436`) is `empty_locals s = s with locals := FEMPTY`. This
    clears `locals` to the empty map (exactly HOL `FEMPTY`, hence `locals` is
    unconditionally finite), but the other `PanSemStateExact` fields remain
    unrestricted `MlS → Option _` functions: the result has whole-state finite
    support only when the input does
    (`PanSemStateExact.finiteSupport_emptyLocals`, which preserves an input
    `FiniteSupport`). Exact finite-map carrier rebuild and tag restoration
    tracked by bead `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def emptyLocalsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with locals := fun _ => none }

@[simp] theorem emptyLocalsHOLExact_locals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) :
    (emptyLocalsHOLExact state).locals name = none := rfl

@[simp] theorem emptyLocalsHOLExact_clock {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).clock = state.clock := rfl

@[simp] theorem emptyLocalsHOLExact_globals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).globals = state.globals := rfl

end Flapjack
