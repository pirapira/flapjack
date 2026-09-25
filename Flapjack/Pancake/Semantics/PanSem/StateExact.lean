import Flapjack.HolRef
import Flapjack.Ffi
import Flapjack.RiscV.Model
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Exact `panSem$state` over the faithful `mlstring` carrier

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
String/MlString carrier rule (`flapjack-0lj`).  This module introduces the
exact carrier `PanSemStateExact` over `MlS` keys, `ShapeHOL`/`StructContextExact`
syntax, `ProgHOL` code and the `ValueHOL` value carrier, and re-establishes the
four state-helper tags exactly over it.

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
    decidability supplied at use sites), and `base_addr`/`top_addr` are words.
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
  ffi : FfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

/-- Exact port of HOL `panSem$dec_clock` (`panSemScript.sml:441`):
    `dec_clock s = s with clock := s.clock - 1`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "dec_clock_def"]
def decClockHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  { state with clock := state.clock - 1 }

/-- Exact port of HOL `panSem$fix_clock` (`panSemScript.sml:446`):
    `fix_clock old_s (res, new_s) = (res, new_s with clock := min old_s.clock
    new_s.clock)`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_def"]
def fixClockHOLExact {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateExact width σ) (step : β × PanSemStateExact width σ) :
    β × PanSemStateExact width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- Exact port of HOL `panSem$lookup_kvar` (`panSemScript.sml:415`): a `Local`
    variable is looked up in `locals`, a `Global` one in `globals`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_kvar_def"]
def lookupKvarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateExact width σ) :
    Option (ValueHOL width) :=
  match kind with
  | .local => state.locals name
  | .global => state.globals name

/-- Exact port of HOL `panSem$set_kvar` (`panSemScript.sml:408-412`): a `Local`
    variable updates `locals`, a `Global` one updates `globals`, via the HOL
    `|+` (counterpart `FUPDATE`, which is `=`-based). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_kvar_def"]
def setKvarHOLExact {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateExact width σ) : PanSemStateExact width σ :=
  match kind with
  | .local =>
      { state with locals := fun current => if current = name then some value else state.locals current }
  | .global =>
      { state with globals := fun current => if current = name then some value else state.globals current }

end Flapjack
