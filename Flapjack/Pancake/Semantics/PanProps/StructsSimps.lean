import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# Exact finite-map projection simplifications for PanProps

Counterpart fragment for the local HOL theorem `panProps$structs_simps`.
The theorem concerns the six state projections produced by `dec_clock` and
`empty_locals`; this module keeps the full HOL state carrier so those are the
same operations and quantified state as the source theorem.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS StructContextExact)

/-- Full Pan semantic state used by this PanProps fragment. The four
    map-valued fields have canonical finite support, as in HOL `|->`. -/
structure PanPropsStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
  locals : HolFiniteMapExact MlS (ValueHOL width)
  globals : HolFiniteMapExact MlS (ValueHOL width)
  structs : StructContextExact
  code : HolFiniteMapExact MlS (List (MlS × Flapjack.Pancake.PanLang.ShapeHOL) ×
    Flapjack.Pancake.PanLang.ProgHOL width × Flapjack.Pancake.PanLang.ShapeHOL)
  eshapes : HolFiniteMapExact MlS Flapjack.Pancake.PanLang.ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

namespace PanPropsStateFiniteExact

variable {width : Nat} {σ : Type} [NeZero width]

/-- Forget the finite-support witnesses into the broad exact carrier. -/
def toPanSemStateExact (state : PanPropsStateFiniteExact width σ) :
    PanSemStateExact width σ where
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

/-- Rebuild the finite-support carrier from a broad state and its exact
    finite-support witness. -/
def ofPanSemStateExact (state : PanSemStateExact width σ)
    (h : state.FiniteSupport) : PanPropsStateFiniteExact width σ where
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

/-- Kernel-checked carrier witness required by the finite-support qualifier. -/
theorem holFmapAsFiniteSupportWitness :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (ofPanSemStateExact state h).toPanSemStateExact = state) ∧
    (∀ state : PanPropsStateFiniteExact width σ,
      ofPanSemStateExact state.toPanSemStateExact
        ⟨state.locals.finiteSupport, state.globals.finiteSupport,
          state.code.finiteSupport, state.eshapes.finiteSupport⟩ = state) := by
  constructor
  · intro state h
    cases state
    rfl
  · intro state
    let broad := state.toPanSemStateExact
    have h : broad.FiniteSupport :=
      ⟨state.locals.finiteSupport, state.globals.finiteSupport,
        state.code.finiteSupport, state.eshapes.finiteSupport⟩
    change ofPanSemStateExact broad h = state
    cases state
    rfl

end PanPropsStateFiniteExact

namespace PanPropsStateFiniteExact

variable {width : Nat} {σ : Type} [NeZero width]

/-- HOL `dec_clock` for the local full-state carrier. -/
def decClock (state : PanPropsStateFiniteExact width σ) :
    PanPropsStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- HOL `empty_locals` for the local full-state carrier. -/
def emptyLocals (state : PanPropsStateFiniteExact width σ) :
    PanPropsStateFiniteExact width σ :=
  { state with locals := HolFiniteMapExact.empty }

end PanPropsStateFiniteExact

/-- HOL `dec_clock` and `empty_locals` projection equations from
    `panPropsScript.sml:1217`. All four HOL finite-map fields are represented
    by `HolFiniteMapExact`; the named qualifier records that carrier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "structs_simps"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem structsSimpsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsStateFiniteExact width σ) :
    (PanPropsStateFiniteExact.decClock state).structs =
        state.structs ∧
    (PanPropsStateFiniteExact.emptyLocals state).structs =
        state.structs ∧
    (PanPropsStateFiniteExact.decClock state).globals =
        state.globals ∧
    (PanPropsStateFiniteExact.emptyLocals state).globals =
        state.globals ∧
    (PanPropsStateFiniteExact.decClock state).locals =
        state.locals ∧
    (PanPropsStateFiniteExact.emptyLocals state).locals =
        HolFiniteMapExact.empty := by
  simp [PanPropsStateFiniteExact.decClock, PanPropsStateFiniteExact.emptyLocals]

end Flapjack
