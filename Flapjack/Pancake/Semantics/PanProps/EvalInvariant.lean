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

/-- Two independent HOL finite-map arguments packaged as fields so the
    canonical `fmap_as_finite_support` qualifier can name each translation. -/
structure PanPropsResVarMapsExact (α β : Type) where
  fm : HolFiniteMapExact α β
  fm2 : HolFiniteMapExact α β

/-- Broad function-map counterpart for the two generic `res_var` inputs. -/
structure PanPropsResVarMapsBroad (α β : Type) where
  fm : FiniteMap α β
  fm2 : FiniteMap α β

namespace PanPropsResVarMapsExact

def toBroad {α β : Type} (maps : PanPropsResVarMapsExact α β) :
    PanPropsResVarMapsBroad α β :=
  ⟨maps.fm.lookup, maps.fm2.lookup⟩

def ofBroad {α β : Type} (maps : PanPropsResVarMapsBroad α β)
    (support : (∃ keys : List α, ∀ key, maps.fm key ≠ none → key ∈ keys) ∧
      ∃ keys : List α, ∀ key, maps.fm2 key ≠ none → key ∈ keys) :
    PanPropsResVarMapsExact α β :=
  ⟨⟨maps.fm, support.1⟩, ⟨maps.fm2, support.2⟩⟩

theorem toBroad_ofBroad {α β : Type} (maps : PanPropsResVarMapsBroad α β)
    (support : (∃ keys : List α, ∀ key, maps.fm key ≠ none → key ∈ keys) ∧
      ∃ keys : List α, ∀ key, maps.fm2 key ≠ none → key ∈ keys) :
    (ofBroad maps support).toBroad = maps := by
  cases maps
  rfl

theorem ofBroad_toBroad {α β : Type} (maps : PanPropsResVarMapsExact α β) :
    ofBroad maps.toBroad ⟨maps.fm.finiteSupport, maps.fm2.finiteSupport⟩ = maps := by
  cases maps with
  | mk fm fm2 =>
      cases fm
      cases fm2
      simp [ofBroad, toBroad]

/-- Canonical finite-map witness for the two generic HOL `fmap` arguments. -/
theorem holFmapAsFiniteSupportWitness {α β : Type} :
    (∀ (maps : PanPropsResVarMapsBroad α β) support,
        (ofBroad maps support).toBroad = maps) ∧
    (∀ maps : PanPropsResVarMapsExact α β,
        ofBroad maps.toBroad ⟨maps.fm.finiteSupport, maps.fm2.finiteSupport⟩ = maps) :=
  ⟨fun maps support => toBroad_ofBroad maps support, fun maps => ofBroad_toBroad maps⟩

end PanPropsResVarMapsExact

/-- `FEVERY P fm` on the finite-support carrier. This pointwise definition
    follows HOL's `FEVERY`/`FLOOKUP` view without adding a membership premise. -/
def feveryHOL {α β : Type} (P : α × β → Bool) (fm : HolFiniteMapExact α β) : Prop :=
  ∀ key value, fm.lookup key = some value → P (key, value) = true

/-- Exact finite-map port of HOL `FEVERY_res_var_FLOOKUP`
    (`panPropsScript.sml:1222`). The two independent HOL map parameters are
    bundled as the product fields `fm` and `fm2`: the broad counterpart stores
    both function maps independently, and the witness roundtrips them without
    relating their contents. Their finite-support proofs are intrinsic to the
    HOL fmap carrier. The qualifier records only this canonical representation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FEVERY_res_var_FLOOKUP"
  (fmap_as_finite_support := [fm, fm2])]
theorem feveryResVarFlookupHOL {α β : Type} [DecidableEq α]
    (P : α × β → Bool) (maps : PanPropsResVarMapsExact α β) (name : α) :
    (feveryHOL P maps.fm ∧ feveryHOL P maps.fm2) →
      feveryHOL P (maps.fm.resVarEq (name, maps.fm2.lookup name)) := by
  intro h
  rcases h with ⟨hfm, hfm2⟩
  intro key value hresult
  cases hlookup : maps.fm2.lookup name with
  | none =>
      by_cases hkey : key = name
      · subst key
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
          FDOMSUB_HOL, hlookup] at hresult
      · have hsource : maps.fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
            FDOMSUB_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource
  | some newValue =>
      by_cases hkey : key = name
      · subst key
        have hvalue : newValue = value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup] using hresult
        subst value
        exact hfm2 name newValue hlookup
      · have hsource : maps.fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource

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

private theorem panMemLoad32HOL_monoDomain {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain1 domain2 : RiscV.Word width → Prop)
    [DecidablePred domain1] [DecidablePred domain2]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hsubset : ∀ current, domain1 current → domain2 current)
    {value : RiscV.Word 32}
    (hload : panMemLoad32HOL memory domain1 bigEndian address = some value) :
    panMemLoad32HOL memory domain2 bigEndian address = some value := by
  unfold panMemLoad32HOL at hload ⊢
  by_cases haligned : address.toNat % 4 = 0
  · simp only [if_pos haligned] at hload ⊢
    cases hmemory : memory (panByteAlignHOL (width := width) address) with
    | word word =>
        simp only [hmemory] at hload ⊢
        by_cases hdomain : domain1 (panByteAlignHOL (width := width) address)
        · simp only [if_pos hdomain] at hload
          have hdomain2 := hsubset _ hdomain
          simp only [if_pos hdomain2]
          exact hload
        · simp [hdomain] at hload
  · simp [haligned] at hload

private theorem evalHOLExactMemaddrsMono {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs]
    (hsubset : ∀ address, state.memaddrs address → memaddrs address) :
    ∀ expression value,
      evalHOLExact state expression = some value →
        evalHOLExact { state with memaddrs := memaddrs } expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields => ∀ values,
        evalListFieldsHOLExact state fields = some values →
          evalListFieldsHOLExact { state with memaddrs := memaddrs } fields = some values)
      (motive_3 := fun expressions => ∀ values,
        evalListHOLExact state expressions = some values →
          evalListHOLExact { state with memaddrs := memaddrs } expressions = some values)
  case case4 fields ih =>
    intro value hEval
    cases hFields : evalListHOLExact state fields with
    | none => simp [evalHOLExact, hFields] at hEval
    | some values =>
        simp only [evalHOLExact, hFields] at hEval
        cases hEval
        simp [evalHOLExact, ih values hFields]
  case case15 shape address hShape word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hLoad : memLoadHOLExact shape word state.memaddrs state.memory state.structs =
        some value := by
      simpa [evalHOLExact, hShape, hAddress] using hEval
    have hLoad' := memLoadHOLExactSwapMemaddrs.1 shape word state.memaddrs
      state.memory state.structs value memaddrs ⟨hLoad, hsubset⟩
    simpa [evalHOLExact, hShape, hAddress'] using hLoad'
  case case18 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : Option.map (fun loaded =>
        .val (.word (BitVec.ofNat width loaded.toNat)))
        (panMemLoad32HOL state.memory state.memaddrs state.be word) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    cases hSource : panMemLoad32HOL state.memory state.memaddrs state.be word with
    | none => simp [hSource] at hRead
    | some loaded =>
        have hValue : ValueHOL.val (.word (BitVec.ofNat width loaded.toNat)) = value := by
          simpa [hSource] using hRead
        have hLoad' := panMemLoad32HOL_monoDomain state.memory state.memaddrs
          memaddrs state.be word hsubset hSource
        simpa [evalHOLExact, hAddress', hLoad'] using hValue
  all_goals
    try intro result hEval
    simp_all [evalHOLExact, evalListHOLExact, evalListFieldsHOLExact,
      panMemLoadByteHOL]

/-- Exact port of HOL `eval_swap_memaddrs`
    (`cakeml/pancake/semantics/panPropsScript.sml:1703-1715`). It keeps HOL's
    conjunction premise and record-update conclusion. The state uses the local
    finite-support carrier and the qualifier records precisely its four HOL
    finite-map fields. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memaddrs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
theorem evalSwapMemaddrsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (state.evalHOL expression = some value ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
          ({ state with memaddrs := memaddrs }.evalHOL expression = some value) := by
  intro state hmemaddrs expression value memaddrs hmemaddrs2 h
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hmemaddrs
  have hEval : evalHOLExact state.toExact expression = some value := by
    simpa [evalHOL] using h.1
  have hWidened := evalHOLExactMemaddrsMono state.toExact memaddrs h.2
    expression value hEval
  simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact] using hWidened

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
