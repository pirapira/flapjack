import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.EvalExact

/-!
Finite-map carrier and expression invariant for the HOL `eval_is_wf_shape_v`
prerequisite to `evaluate_is_wf_shape_invariant`. This submodule sits under
the `panPropsScript.sml` counterpart; its carrier owns the map fields named by
the representation qualifier and is invertibly related to `PanSemStateExact`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS StructContextExact ProgHOL ExpHOL ShapeHOL)

/-- PanProps-local finite-map rendering of HOL's PanSem state. The four
    `HolFiniteMapExact` fields correspond to HOL `|->` fields; all other fields
    retain the exact PanSem carrier types. -/
structure PanPropsEvalStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
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

namespace PanPropsEvalStateFiniteExact

/-- Forget the finite-map witnesses and expose the exact broad state. -/
def toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : PanSemStateExact width σ where
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

/-- Build this finite-map carrier from a broad state with finite support. -/
def ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    PanPropsEvalStateFiniteExact width σ where
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

theorem toExact_ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (ofExact state h).toExact = state := rfl

theorem toExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : state.toExact.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport,
    state.code.finiteSupport, state.eshapes.finiteSupport⟩

theorem ofExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    ofExact state.toExact state.toExact_finiteSupport = state := by
  cases state
  rfl

/-- Checked canonical witness for this module's finite-map field qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩

/-- Finite-support carrier rendering of HOL `eval_def`. -/
def evalHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- Exact port of HOL `panProps$eval_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:126`). The conjunction
    preserves HOL's successful-evaluation, `FEVERY locals`, `FEVERY globals`
    hypothesis order. Finite-map fields use the reviewed canonical
    `HolFiniteMapExact` translation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_is_wf_shape_v"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalIsWfShapeValueHOL {width : Nat} {σ : Type} [NeZero width]
    :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width),
      state.evalHOL expression = some value ∧
        (∀ name bound, state.locals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) ∧
        (∀ name bound, state.globals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) →
        isWfShapeValueHOLExact state.structs value = true := by
  intro state hdec expression value h
  have hEval := h.1
  have hlocals := h.2.1
  have hglobals := h.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  apply evalHOLExact_isWfShapeValueHOLExact state.toExact hlocals hglobals expression value
  simpa [evalHOL] using hEval

end PanPropsEvalStateFiniteExact

end Flapjack
