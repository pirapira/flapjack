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

  Statement/side-condition review for `flapjack-pxn.18.3.7.1.3.1.1.2`
  (2026-09-25): the five HOL definitions
  (`cakeml/pancake/semantics/panSemScript.sml:396-449`) quantify the state
  component as a finite map `varname |-> v`, written with `FUPDATE`/`FLOOKUP`,
  whereas `PanSemStateFiniteExact` carries a `HolFiniteMapExact` value (a
  `lookup` function together with a `finiteSupport` proof).  `HolFiniteMapExact`
  is the reviewed *standard* Lean translation of HOL's finite map: it is closed,
  extensional (see `HolFiniteMapExact.ext`), and invertible with the
  finite-support subtype of the broad `PanSemStateExact` carrier (see
  `PanSemStateFiniteExact.ofExact` / `toExact` and the canonical witness
  `holFmapAsFiniteSupportWitness`).  The representation is now recorded by the
  `@[hol ...]` qualifier `fmap_as_finite_support` implemented in
  `Flapjack/HolRef.lean` and enforced by `scripts/check-hol-refs.py`; it is a
  representation statement only and does not authorize changed quantifiers,
  hypotheses, results, `BEq` side conditions, or word-model differences.  The
  five `...HOLFinite` helpers remain untagged: each is still reviewed
  case-by-case under `flapjack-pxn.18.3.7.1.3.1.1.2.4`.  The broad-carrier
  helpers over `PanSemStateExact` (`StateExact.lean`) remain the
  `documented_mismatch` analogues.

  Nothing here is tagged `@[hol]` yet: this is representation infrastructure for
  the exact-carrier rebuild tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`; the
  tag qualifier itself is `flapjack-pxn.18.3.7.1.3.1.1.2.4`.
-/

import Flapjack.Pancake.Semantics.PanSem.StateExactFinite

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ProgHOL)

/-- `HolFiniteMapExact` is extensional: two values with the same `lookup` are
    equal, because the `finiteSupport` field is a proof of a proposition.  This
    is the extensionality half of the canonical finite-map translation witness. -/
theorem HolFiniteMapExact.ext {α β : Type} {left right : HolFiniteMapExact α β}
    (h : left.lookup = right.lookup) : left = right := by
  obtain ⟨lleft, pleft⟩ := left
  obtain ⟨lright, pright⟩ := right
  simp only at h
  subst h
  rfl

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

/-- Rebuild the finite-support carrier from a broad exact state together with a
    finite-support proof: each unrestricted lookup function becomes a
    `HolFiniteMapExact` using the supplied witness.  This is the inverse of
    `toExact` on the finite-support subtype. -/
def ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    PanSemStateFiniteExact width σ where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  structs := state.structs
  code := { lookup := state.code, finiteSupport := h.2.2.1 }
  eshapes := { lookup := state.eshapes, finiteSupport := h.2.2.2 }
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- One roundtrip: `toExact` after `ofExact` is the identity on a finite-support
    broad state. -/
theorem toExact_ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (ofExact state h).toExact = state :=
  rfl

/-- The other roundtrip: `ofExact` after `toExact` is the identity on the
    finite-support carrier.  The `finiteSupport` proofs are propositionally
    irrelevant. -/
theorem ofExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    ofExact state.toExact state.toExact_finiteSupport = state := by
  cases state
  rfl

/-- Canonical global kernel witness for the `fmap_as_finite_support` `@[hol]`
    qualifier: `HolFiniteMapExact` is extensional and the finite-support carrier
    is invertibly related to the broad exact one.  The checker requires this
    declaration in the module of a `fmap_as_finite_support`-qualified tag. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩


def decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- The finite-support dec-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.decClockHOLFinite.toExact = decClockHOLExact state.toExact :=
  rfl

/-- Finite-support mirror of `fixClockHOLExact`.  Untagged: the exact-carrier
    retag is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def fixClockHOLFinite {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    β × PanSemStateFiniteExact width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- The finite-support fix-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_fixClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    {β : Type} (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    (fixClockHOLFinite oldState step).2.toExact =
      (fixClockHOLExact oldState.toExact (step.1, step.2.toExact)).2 :=
  rfl

/-- Finite-support mirror of `lookupKvarHOLExact`.  Untagged: the exact-carrier
    retag is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def lookupKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateFiniteExact width σ) :
    Option (ValueHOL width) :=
  match kind with
  | .local => state.locals.lookup name
  | .global => state.globals.lookup name

/-- The finite-support keyed-variable lookup is compatible with the broad exact
    one. -/
@[simp] theorem lookupKvarHOLFinite_eq {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (state : PanSemStateFiniteExact width σ) :
    lookupKvarHOLFinite kind name state =
      lookupKvarHOLExact kind name state.toExact := by
  cases kind <;> rfl

/-- Finite-support mirror of `setKvarHOLExact`.  The updated component keeps a
    finite support by consing the written key onto the old support.  Untagged:
    the exact-carrier retag is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  match kind with
  | .local =>
      { state with
        locals :=
          { lookup := fun current =>
              if current = name then some value else state.locals.lookup current
            finiteSupport := by
              obtain ⟨keys, hkeys⟩ := state.locals.finiteSupport
              refine ⟨name :: keys, ?_⟩
              intro key hkey
              by_cases h : key = name
              · rw [← h]; exact List.mem_cons_self
              · exact List.mem_cons_of_mem name (hkeys key (by simpa [h] using hkey)) } }
  | .global =>
      { state with
        globals :=
          { lookup := fun current =>
              if current = name then some value else state.globals.lookup current
            finiteSupport := by
              obtain ⟨keys, hkeys⟩ := state.globals.finiteSupport
              refine ⟨name :: keys, ?_⟩
              intro key hkey
              by_cases h : key = name
              · rw [← h]; exact List.mem_cons_self
              · exact List.mem_cons_of_mem name (hkeys key (by simpa [h] using hkey)) } }

/-- The finite-support keyed-variable write is compatible with the broad exact
    one. -/
@[simp] theorem toExact_setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) :
    (setKvarHOLFinite kind name value state).toExact =
      setKvarHOLExact kind name value state.toExact := by
  cases kind <;> rfl

/-- Finite-support mirror of `emptyLocalsHOLExact`.  Untagged: the exact-carrier
    retag is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2`. -/
def emptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with
    locals :=
      { lookup := fun _ => none
        finiteSupport := ⟨[], by intro key hkey; exact absurd rfl hkey⟩ } }

/-- The finite-support locals-clearing is compatible with the broad exact
    one. -/
@[simp] theorem toExact_emptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    (emptyLocalsHOLFinite state).toExact = emptyLocalsHOLExact state.toExact :=
  rfl

end PanSemStateFiniteExact

end Flapjack
