import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep

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

/-- Local finite-map `dec_clock` operation for the projection equations below. -/
def decClockForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- Local finite-map `empty_locals` operation for the projection equations. -/
def emptyLocalsForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with locals := HolFiniteMapExact.empty }

/-- HOL `panProps$structs_simps` (`panPropsScript.sml:1217`): the six
    projections of `dec_clock` and `empty_locals`. This uses the existing
    PanProps finite-map state and its canonical same-module roundtrip witness. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "structs_simps"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem structsSimpsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    (decClockForStructsSimps state).structs = state.structs ∧
    (emptyLocalsForStructsSimps state).structs = state.structs ∧
    (decClockForStructsSimps state).globals = state.globals ∧
    (emptyLocalsForStructsSimps state).globals = state.globals ∧
    (decClockForStructsSimps state).locals = state.locals ∧
    (emptyLocalsForStructsSimps state).locals = HolFiniteMapExact.empty := by
  simp [decClockForStructsSimps, emptyLocalsForStructsSimps]

/-- Finite-support carrier rendering of HOL `eval_def`. -/
def evalHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- `OPT_MMAP eval` over the same finite-support carrier. -/
def evalListHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact (by
    simpa [PanPropsEvalStateFiniteExact.toExact] using h)

/-- PanProps proof support that assembles the finite-map `lookup_code` result
    needed by `lookup_code_wf_shape_invariant_step`. The underlying HOL
    `lookup_code_def` is in `panSemScript.sml:458-467`; this helper is untagged
    because it is an invariant-proof wrapper in the PanProps counterpart. -/
def lookupCodeHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (fname : MlS)
    (arguments : List (ValueHOL width)) :
    Option (ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) :=
  match state.code.lookup fname with
  | none => none
  | some (parameters, body, returnShape) =>
      if (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true then
        some (body,
          HolFiniteMapExact.empty.updateList ((parameters.map Prod.fst).zip arguments),
          returnShape)
      else none

/-- Exact port of HOL `panProps$eval_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:126`). The conjunction
    preserves HOL's successful-evaluation, `FEVERY locals`, `FEVERY globals`
    hypothesis order. Finite-map fields use the reviewed canonical
    `HolFiniteMapExact` translation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_is_wf_shape_v"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalIsWfShapeValueHOL {width : Nat} {σ : Type} [NeZero width] :
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

private theorem snd_mem_of_mem_zip {α β : Type} {left : List α} {right : List β}
    {pair : α × β} (h : pair ∈ left.zip right) : pair.2 ∈ right := by
  induction left generalizing right pair with
  | nil => simp at h
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons head' tail' =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with heq | htail
          · cases heq
            simp
          · exact List.mem_cons_of_mem head' (ih htail)

private theorem evalListHOLExact_mem_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (hlocals : ∀ name value, state.locals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (hglobals : ∀ name value, state.globals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true) :
    ∀ expressions values,
      state.evalListHOL expressions = some values →
        ∀ value, value ∈ values → isWfShapeValueHOLExact state.structs value = true := by
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using
      (inferInstance : DecidablePred state.memaddrs)
  intro expressions
  induction expressions with
  | nil =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact [] = some values at hEval
      simp [evalListHOLExact] at hEval
      cases hEval
      simp at hmem
  | cons expression rest ih =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact (expression :: rest) = some values at hEval
      cases hExpression : evalHOLExact state.toExact expression with
      | none => simp [evalListHOLExact, hExpression] at hEval
      | some head =>
          cases hRest : evalListHOLExact state.toExact rest with
          | none => simp [evalListHOLExact, hExpression, hRest] at hEval
          | some tail =>
              have hSomeValues : some (head :: tail) = some values := by
                simpa only [evalListHOLExact, hExpression, hRest] using hEval
              have hValues : head :: tail = values := Option.some.inj hSomeValues
              subst values
              simp only [List.mem_cons] at hmem
              rcases hmem with hHead | hmem
              · subst value
                have hExpressionFinite : state.evalHOL expression = some head := by
                  simpa [evalHOL] using hExpression
                exact evalIsWfShapeValueHOL state expression head
                  ⟨hExpressionFinite, hlocals, hglobals⟩
              · exact ih tail (by simpa [evalListHOL] using hRest) value hmem

/-- HOL `lookup_code_wf_shape_invariant_step` proof dependency: evaluated
    arguments are well-formed, so every value installed into the callee's
    finite locals map is well-formed. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "lookup_code_wf_shape_invariant_step"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem lookupCodeWfShapeInvariantStep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (argexps : List (ExpHOL width)) (args : List (ValueHOL width))
      (fname : MlS) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      state.evalListHOL argexps = some args ∧
        lookupCodeHOLFinite state fname args = some (prog, newlocals, returnShape) ∧
        (∀ name value, state.locals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) ∧
        (∀ name value, state.globals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) →
        (∀ name value, newlocals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) := by
  intro state hdec argexps args fname prog newlocals returnShape h
  have hArgs := h.1
  have hLookup := h.2.1
  have hlocals := h.2.2.1
  have hglobals := h.2.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  cases hCode : state.code.lookup fname with
  | none => simp [lookupCodeHOLFinite, hCode] at hLookup
  | some codeEntry =>
      rcases codeEntry with ⟨parameters, body, declaredReturn⟩
      by_cases hValid : (parameters.map Prod.fst).Nodup ∧
          parameters.length = args.length ∧
          ((parameters.zip args).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
      · have hResult :
            some (body, HolFiniteMapExact.empty.updateList
              ((parameters.map Prod.fst).zip args), declaredReturn) =
              some (prog, newlocals, returnShape) := by
          simpa [lookupCodeHOLFinite, hCode, hValid] using hLookup
        have hTuple := Option.some.inj hResult
        have hMap : HolFiniteMapExact.empty.updateList
            ((parameters.map Prod.fst).zip args) = newlocals :=
          congrArg Prod.fst (congrArg Prod.snd hTuple)
        have hMapLookup := congrArg HolFiniteMapExact.lookup hMap
        intro name value hValue
        have hFold :
            FUPDATE_LIST (FEMPTY : FiniteMap MlS (ValueHOL width))
              ((parameters.map Prod.fst).zip args) name = some value := by
          rw [← hMapLookup] at hValue
          change FUPDATE_LIST (fun _ => none)
            ((parameters.map Prod.fst).zip args) name = some value
          simpa [HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FEMPTY] using hValue
        have hEntries := flookupFupdateList_mem_or_base
          (FEMPTY : FiniteMap MlS (ValueHOL width))
          ((parameters.map Prod.fst).zip args) name value (by
            simpa [FLOOKUP] using hFold)
        rcases hEntries with ⟨entry, hentry, _, hentryValue⟩ | hbase
        · subst value
          exact evalListHOLExact_mem_isWf state hlocals hglobals argexps args hArgs
            entry.2 (snd_mem_of_mem_zip hentry)
        · simp [FLOOKUP, FEMPTY] at hbase
      · have hLookup' := hLookup
        simp [lookupCodeHOLFinite, hCode] at hLookup'
        have hValid' : (parameters.map Prod.fst).Nodup ∧
            parameters.length = args.length ∧
            ((parameters.zip args).all
              (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
          refine ⟨hLookup'.1.1, hLookup'.1.2.1, List.all_eq_true.mpr ?_⟩
          intro pair hpair
          exact hLookup'.1.2.2 pair.1.1 pair.1.2 pair.2 hpair
        exact False.elim (hValid hValid')

end PanPropsEvalStateFiniteExact

end Flapjack
