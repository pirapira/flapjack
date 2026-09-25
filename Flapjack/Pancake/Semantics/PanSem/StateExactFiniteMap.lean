/-
  Finite-support PanSem state carrier.

  HOL `panSem$state` stores its `locals`, `globals`, `code` and `eshapes`
  components as finite maps (`|->`).  `PanSemStateExact` instead quantifies
  them as unrestricted lookup functions (`MlS → Option _`), which is a strict
  superset of the finite-map carriers.  The five exact state helpers
  (`dec_clock`, `fix_clock`, `lookup_kvar`, `set_kvar`, `empty_locals`) were
  therefore withdrawn from `@[hol]` tagging at audit
  `flapjack-pxn.18.3.7.1.3.1.2`; this module provides a carrier that is
  finite-support *by type* so those helpers can be restated faithfully and
  retagged later.

  Nothing here is tagged `@[hol]`: this is representation infrastructure for
  the exact-carrier rebuild tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`.
-/

import Flapjack.Pancake.Semantics.PanSem.StateExactFinite

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ProgHOL)

/-- Finite-support mirror of `PanSemStateExact`.  The four map-shaped
    components are `HolFiniteMapExact` values, i.e. finite support holds by
    construction, matching HOL's `|->` fields. -/
structure PanSemStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
  locals : HolFiniteMapExact MlS (ValueHOL width)
  globals : HolFiniteMapExact MlS (ValueHOL width)
  structs : StructContextExact
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  eshapes : HolFiniteMapExact MlS ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

namespace PanSemStateFiniteExact

/-- Forget the finite-support witnesses, reading every map through `.lookup`. -/
def toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateExact width σ where
  locals := state.locals.lookup
  globals := state.globals.lookup
  structs := state.structs
  code := state.code.lookup
  eshapes := state.eshapes.lookup
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The forgetful projection lands in the finite-support subtype of the broad
    exact carrier. -/
theorem toExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.toExact.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport,
    state.code.finiteSupport, state.eshapes.finiteSupport⟩

/-- Finite-support mirror of `decClockHOLExact`.  Untagged: the exact-carrier
    retag is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- The finite-support dec-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.decClockHOLFinite.toExact = decClockHOLExact state.toExact :=
  rfl

end PanSemStateFiniteExact

end Flapjack
