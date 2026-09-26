/-
  Finite-support PanSem state carrier.

  HOL `panSem$state` stores its `locals`, `globals`, `code` and `eshapes`
  components as finite maps (`|->`).  `PanSemStateExact` instead quantifies
  them as unrestricted lookup functions (`MlS → Option _`), which is a strict
  superset of the finite-map carriers. Five exact state helpers
  (`dec_clock`, `fix_clock`, `lookup_kvar`, `set_kvar`, `empty_locals`) were
  temporarily withdrawn from `@[hol]` tagging at audit
  `flapjack-pxn.18.3.7.1.3.1.2`. This module provides a carrier that is
  finite-support *by type*; those five and the `set_var`/`set_global` helpers
  have since been reviewed and tagged over it.

  Statement/side-condition review for `flapjack-pxn.18.3.7.1.3.1.1.2`
  (2026-09-25): the five HOL definitions
  (`cakeml/pancake/semantics/panSemScript.sml:396-449`) quantify the state
  component as a finite map `varname |-> v`, written with `FUPDATE`/`FLOOKUP`,
  whereas `PanSemStateFiniteExact` carries a   `HolFiniteMapExact` value (a
  `lookup` function together with a `finiteSupport` proof).  `HolFiniteMapExact`
  is the reviewed *standard* Lean translation of HOL's finite map: it is closed,
  extensional (see `HolFiniteMapExact.ext`), and invertible with the
  finite-support subtype of the broad `PanSemStateExact` carrier (see
  `PanSemStateFiniteExact.ofExact` / `toExact` and the canonical witness
  `holFmapAsFiniteSupportWitness`).  The representation is recorded by the
  `@[hol ...]` qualifier `fmap_as_finite_support` implemented in
  `Flapjack/HolRef.lean` and enforced by `scripts/check-hol-refs.py`; it is a
  representation statement only and does not authorize changed quantifiers,
  hypotheses, results, `BEq` side conditions, or word-model differences.

  Seven helper definitions have passed their case-by-case review and carry
  `@[hol ...]` with that qualifier: `decClockHOLFinite` (`dec_clock_def`),
  `fixClockHOLFinite` (`fix_clock_def`), `lookupKvarHOLFinite` (`lookup_kvar_def`),
  `emptyLocalsHOLFinite` (`empty_locals_def`) and `setKvarHOLFinite`
  (`set_kvar_def`), plus `setVarHOLFinite` (`set_var_def`) and
  `setGlobalHOLFinite` (`set_global_def`). `setKvarHOLFinite` routes through
  these canonical-update helpers, which use
  `HolFiniteMapExact.update` (`FUPDATE`) exactly like HOL `set_var`/`set_global`;
  the `MlS` `BEq`/`LawfulBEq` instances required by `update` are declared below.
  The broad-carrier helpers over `PanSemStateExact` (`StateExact.lean`) remain the
  `documented_mismatch` analogues.  Work tracked by
  `flapjack-pxn.18.3.7.1.3.1.1.2.4`.

  Word-model review for `flapjack-pxn.18.3.7.1.3.1.1.2.4.6` (2026-09-25): HOL
  types the state components over `'a word` for an arbitrary finite type `'a`
  (the `finite_index` class; `panSemScript.sml:48-63` uses `'a word` for
  `memory`/`base_addr`/`top_addr` and `'a word_lab` for the memory values), while
  this module uses `RiscV.Word width` (`= BitVec width`, `RiscV/Model.lean:17`)
  together with `[NeZero width]` and `HolWordLab width`.  A HOL finite type is
  nonempty, so `dimindex 'a >= 1`, and the positive-width `BitVec width` carrier
  is the standard faithful translation of `'a word` (with `HolWordLab` its
  `word_lab` wrapper).  The five helpers themselves are word-agnostic: they only
  read/write `clock` and the finite-map fields, so they add no word-model side
  condition; `[NeZero width]` mirrors HOL nonemptiness and is a carrier artifact,
  not a changed side condition of the tagged definitions.
-/

import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ProgHOL ExpHOL)

/-- `HolFiniteMapExact` is extensional: two values with the same `lookup` are
    equal, because the `finiteSupport` field is a proof of a proposition.  This
    is separate from the canonical roundtrip witness below. -/
theorem HolFiniteMapExact.ext {α β : Type} {left right : HolFiniteMapExact α β}
    (h : left.lookup = right.lookup) : left = right := by
  obtain ⟨lleft, pleft⟩ := left
  obtain ⟨lright, pright⟩ := right
  simp only at h
  subst h
  rfl

/-- `MlString` only derives `DecidableEq`; the canonical `FUPDATE`-based finite-map
    operations need a `BEq`/`LawfulBEq` instance, so boolean equality is the
    decidability test.  Declared here as representation infrastructure (additive:
    `MlS` had no `BEq` instance before). -/
instance : BEq MlS where
  beq left right := decide (left = right)

instance : LawfulBEq MlS where
  eq_of_beq h := of_decide_eq_true h

/-- Reading `HolFiniteMapExact.update` (`FUPDATE`) pointwise.  The canonical
    update's `if name == current` is the same test as the pointwise
    `if current = name` used by the broad `set_var`/`set_global` mirrors. -/
theorem HolFiniteMapExact.lookup_update_pointwise {α β : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] (map : HolFiniteMapExact α β) (name : α) (value : β) :
    (map.update (name, value)).lookup =
      fun current => if current = name then some value else map.lookup current := by
  funext current
  by_cases h : current = name
  · subst h
    simp [HolFiniteMapExact.update, FUPDATE]
  · have hbeq : (name == current) = false := by
      cases hb : (name == current) with
      | true => exact absurd (beq_iff_eq.mp hb) (fun hc => h hc.symm)
      | false => rfl
    simp [HolFiniteMapExact.update, FUPDATE, hbeq, h]

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
@[reducible] def toExact {width : Nat} {σ : Type} [NeZero width]
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
    qualifier: the finite-support carrier is invertibly related to the broad
    exact one. Extensionality is the separate `HolFiniteMapExact.ext` theorem.
    The checker requires this
    declaration in the module of a `fmap_as_finite_support`-qualified tag. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩


/-- HOL `dec_clock_def` (`cakeml/pancake/semantics/panSemScript.sml:441-444`):
    `dec_clock s = s with clock := s.clock - 1`.  The body matches clause for
    clause; the state carrier's four finite-map fields (`locals`, `globals`,
    `code`, `eshapes`) are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
def decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- The finite-support dec-clock is compatible with the broad exact one. -/
@[simp] theorem toExact_decClockHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) :
    state.decClockHOLFinite.toExact = decClockHOLExact state.toExact :=
  rfl

/-- HOL `fix_clock_def` (`cakeml/pancake/semantics/panSemScript.sml:446-449`):
    `fix_clock old_s (res, new_s) = (res, new_s with clock := if old_s.clock <
    new_s.clock then old_s.clock else new_s.clock)`.  The pair result and the
    clamped clock match clause for clause; the four finite-map fields are
    recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
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

/-- HOL `lookup_kvar_def` (`cakeml/pancake/semantics/panSemScript.sml:415-420`):
    `lookup_kvar vk v s = case vk of Local => FLOOKUP s.locals v | Global =>
    FLOOKUP s.globals v`.  The two branches match; `HolFiniteMapExact.lookup` is
    the standard Lean translation of `FLOOKUP` and the carrier's finite-map
    fields are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_kvar_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
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

/-- HOL `set_var_def` (`cakeml/pancake/semantics/panSemScript.sml:398-401`):
    `set_var v value s = s with locals := s.locals |+ (v,value)`.  The `|+`
    (FUPDATE) is the canonical `HolFiniteMapExact.update` on the finite-support
    carrier.  The `locals`/`globals`/`code`/`eshapes` fields are the canonical
    finite-map representation, recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness` in this
    module). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
def setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with locals := state.locals.update (name, value) }

/-- HOL `set_global_def` (`cakeml/pancake/semantics/panSemScript.sml:403-406`):
    `set_global v value s = s with globals := s.globals |+ (v,value)`, i.e. the
    canonical `HolFiniteMapExact.update` on the `globals` component.  Its
    finite-map fields are recorded by the `fmap_as_finite_support` qualifier
    (canonical witness `holFmapAsFiniteSupportWitness` in this module). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_global_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
def setGlobalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with globals := state.globals.update (name, value) }

/-- HOL `set_kvar_def` (`cakeml/pancake/semantics/panSemScript.sml:408-413`):
    `set_kvar vk v value s = case vk of Local => set_var v value s
    | Global => set_global v value s`.  Body-exact over `PanSemStateFiniteExact`
    via the canonical-update wrappers above.  The `locals`/`globals`/`code`/
    `eshapes` fields are the canonical finite-map representation, recorded by the
    `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "set_kvar_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
def setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) : PanSemStateFiniteExact width σ :=
  match kind with
  | .local => setVarHOLFinite name value state
  | .global => setGlobalHOLFinite name value state

/-- The finite-support keyed-variable write is compatible with the broad exact
    one. -/
@[simp] theorem toExact_setKvarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (state : PanSemStateFiniteExact width σ) :
    (setKvarHOLFinite kind name value state).toExact =
      setKvarHOLExact kind name value state.toExact := by
  cases kind
  · simp only [setKvarHOLFinite, setVarHOLFinite, setKvarHOLExact,
      PanSemStateFiniteExact.toExact]
    rw [HolFiniteMapExact.lookup_update_pointwise]
  · simp only [setKvarHOLFinite, setGlobalHOLFinite, setKvarHOLExact,
      PanSemStateFiniteExact.toExact]
    rw [HolFiniteMapExact.lookup_update_pointwise]

/-- HOL `empty_locals_def` (`cakeml/pancake/semantics/panSemScript.sml:437-439`):
    `empty_locals s = s with locals := FEMPTY`.  The cleared `locals` is the
    canonical empty finite map (`HolFiniteMapExact.empty`); the carrier's
    finite-map fields are recorded by the `fmap_as_finite_support` qualifier. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "empty_locals_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
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

/-- The finite-support local write is compatible with the broad exact one. -/
@[simp] theorem toExact_setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setVarHOLFinite name value state).toExact = setVarHOLExact name value state.toExact := by
  simp only [setVarHOLFinite, setVarHOLExact, PanSemStateFiniteExact.toExact]
  rw [HolFiniteMapExact.lookup_update_pointwise]

/-- The finite-support global write is compatible with the broad exact one. -/
@[simp] theorem toExact_setGlobalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    (setGlobalHOLFinite name value state).toExact = setGlobalHOLExact name value state.toExact := by
  simp only [setGlobalHOLFinite, setGlobalHOLExact, PanSemStateFiniteExact.toExact]
  rw [HolFiniteMapExact.lookup_update_pointwise]

/-- The finite-support local restore is compatible with the broad exact one. -/
@[simp] theorem lookup_resVarEq_toExact {width : Nat} [NeZero width]
    (map : HolFiniteMapExact MlS (ValueHOL width))
    (entry : MlS × Option (ValueHOL width)) :
    (HolFiniteMapExact.resVarEq map entry).lookup = resVarHOLExact map.lookup entry := by
  obtain ⟨key, valueOpt⟩ := entry
  cases valueOpt with
  | none =>
      funext current
      simp only [HolFiniteMapExact.resVarEq, resVarHOLExact,
        HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  | some value =>
      funext current
      simp only [HolFiniteMapExact.resVarEq, resVarHOLExact,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- HOL `eval_def` (`cakeml/pancake/semantics/panSemScript.sml:209-283`) over the
    finite-support state carrier.  The body delegates to the exact broad
    evaluator through the canonical translation `toExact`; it does NOT
    syntactically present HOL's clause-shaped definition body.  The clause-shaped
    equations in `Flapjack/Pancake/Semantics/PanSem/EvalFinite.lean` expose each
    of the fifteen HOL clauses one by one over this carrier, and the state's four
    finite-map fields (`locals`, `globals`, `code`, `eshapes`) are recorded by the
    `fmap_as_finite_support` qualifier (canonical `HolFiniteMapExact`
    translation, witness `holFmapAsFiniteSupportWitness`). -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "eval_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])]
def evalHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- Finite-support carrier rendering of the `OPT_MMAP eval` list step; delegates
    through `toExact` (untagged helper, not a HOL declaration). -/
def evalListHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact h

/-- Finite-support carrier rendering of the named-struct field-expression step;
    delegates through `toExact` (untagged helper, not a HOL declaration). -/
def evalListFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (MlS × ExpHOL width) → Option (List (MlS × ValueHOL width)) :=
  @evalListFieldsHOLExact width σ _ state.toExact h

/-- Projection equality: the tagged finite-support evaluator is the broad exact
    evaluator applied to `toExact`, i.e. the canonical translation is used. -/
@[simp] theorem evalHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) :
    state.evalHOLFinite expression =
      @evalHOLExact width σ _ state.toExact h expression := rfl

@[simp] theorem evalListHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) :
    state.evalListHOLFinite expressions =
      @evalListHOLExact width σ _ state.toExact h expressions := rfl

@[simp] theorem evalListFieldsHOLFinite_eq_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    state.evalListFieldsHOLFinite fields =
      @evalListFieldsHOLExact width σ _ state.toExact h fields := rfl

/-- FLAPJACK-SPECIFIC ADAPTER (not itself the tagged HOL `evaluate_def` port):
    it runs the broad, context-returning exact evaluator
    `evalPanSemRecursiveCallContextHOLExact` on the forgetful projection
    `toExact`, then rebuilds the resulting state as a finite-support value via
    `ofExact`, using the result-state preservation theorem
    `evalPanSemRecursiveCallContextHOLExact_finiteSupport`.  Because it returns
    the assembly-marked `Option (Option PanSemResultExact × state)` pair and
    reconstructs the state through `ofExact`, this declaration is deliberately
    untagged.  A faithful tagged `evaluate_def` port over the finite-support
    carrier requires a finite eval context that threads
    `memaddrsDecidable`/`shMemaddrsDecidable`; tracked by `flapjack-6yq`. -/
def evalPanSemRecursiveCallHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
  | program =>
      match hres : evalPanSemRecursiveCallContextHOLExact program
          { state := state.toExact
            memaddrsDecidable := h
            shMemaddrsDecidable := hshared } with
      | none => none
      | some pair =>
          some (pair.1,
            ofExact pair.2.state
              (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
                { state := state.toExact
                  memaddrsDecidable := h
                  shMemaddrsDecidable := hshared }
                state.toExact_finiteSupport pair hres))

/-- Projecting the finite recursive evaluator back through `toExact` recovers the
    broad exact evaluator, so the wrapper uses the canonical finite-map
    translation of the state carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    (evalPanSemRecursiveCallHOLFinite state program).map
        (fun pair => (pair.1, pair.2.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact
          memaddrsDecidable := h
          shMemaddrsDecidable := hshared }).map
        (fun pair => (pair.1, pair.2.state)) := by
  unfold evalPanSemRecursiveCallHOLFinite
  dsimp only
  split <;> simp_all only [Option.map_some, toExact_ofExact] <;> rfl

/-- The finite-support recursive evaluator is total: its assembly marker is
    always `some`, so it is a genuine `result × post-state` evaluator over the
    exact finite-map state carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_exists {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    ∃ pair, evalPanSemRecursiveCallHOLFinite state program = some pair := by
  obtain ⟨output, houtput⟩ :=
    evalPanSemRecursiveCallContextHOLExact_total program
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
  cases hv : evalPanSemRecursiveCallHOLFinite state program with
  | none =>
      have hproj := evalPanSemRecursiveCallHOLFinite_toExact state program
      rw [hv] at hproj
      simp only [Option.map_none] at hproj
      rw [houtput] at hproj
      simp at hproj
  | some pair => exact ⟨pair, rfl⟩

/-- Finite-support projection of the reviewed nonrecursive `evaluate_def` clause
    dispatcher `evalPanSemNonrecursiveHOLExact`: it runs the dispatcher on
    `state.toExact` and rebuilds the post-state as a finite-support value using
    `evalPanSemNonrecursiveHOLExact_finiteSupport`. -/
def evalPanSemNonrecursiveHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :=
  match hres : evalPanSemNonrecursiveHOLExact program state.toExact with
  | none => none
  | some pair =>
      some (pair.1, ofExact pair.2
        (evalPanSemNonrecursiveHOLExact_finiteSupport program state.toExact
          state.toExact_finiteSupport pair hres))

/-- Forgetting the finite support of the finite nonrecursive dispatcher recovers
    the broad exact dispatcher transported along `toExact`. -/
theorem evalPanSemNonrecursiveHOLFinite_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    (evalPanSemNonrecursiveHOLFinite state program).map
        (fun pair => (pair.1, pair.2.toExact)) =
      (evalPanSemNonrecursiveHOLExact program state.toExact).map
        (fun pair => (pair.1, pair.2)) := by
  unfold evalPanSemNonrecursiveHOLFinite
  split <;> simp_all only [Option.map_some, toExact_ofExact] <;> rfl

/-- Flapjack-specific finite-carrier invariant: the nonrecursive dispatcher
    preserves `memaddrs`, with the post-state rebuilt through `ofExact`.
    HOL has no standalone declaration for this adapter theorem. -/
theorem evalPanSemNonrecursiveHOLFinite_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (hout : evalPanSemNonrecursiveHOLFinite state program = some output) :
    output.2.memaddrs = state.memaddrs := by
  unfold evalPanSemNonrecursiveHOLFinite at hout
  split at hout
  · simp at hout
  · rename_i pair hres
    simp only [Option.some.injEq] at hout
    subst hout
    have hpair := evalPanSemNonrecursiveHOLExact_memaddrs program state.toExact pair hres
    change pair.2.memaddrs = state.toExact.memaddrs
    exact hpair

/-- Flapjack-specific finite-carrier `shMemaddrs` preservation theorem for the
    nonrecursive dispatcher; no standalone HOL declaration has this shape. -/
theorem evalPanSemNonrecursiveHOLFinite_shMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (hout : evalPanSemNonrecursiveHOLFinite state program = some output) :
    output.2.shMemaddrs = state.shMemaddrs := by
  unfold evalPanSemNonrecursiveHOLFinite at hout
  split at hout
  · simp at hout
  · rename_i pair hres
    simp only [Option.some.injEq] at hout
    subst hout
    have hpair := evalPanSemNonrecursiveHOLExact_shMemaddrs program state.toExact pair hres
    change pair.2.shMemaddrs = state.toExact.shMemaddrs
    exact hpair

/-- Finite nonrecursive dispatcher on `Skip`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.skip : ProgHOL width) = some (none, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- Finite nonrecursive dispatcher on `Break`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.break : ProgHOL width) =
      some (some .break, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- Finite nonrecursive dispatcher on `Continue`. -/
@[simp] theorem evalPanSemNonrecursiveHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evalPanSemNonrecursiveHOLFinite state (.continue : ProgHOL width) =
      some (some .continue, state) := by
  unfold evalPanSemNonrecursiveHOLFinite
  simp [evalPanSemNonrecursiveHOLExact, ofExact_toExact]

/-- FLAPJACK-SPECIFIC (not the tagged HOL `evaluate_def` port): finite-support
    rendering of HOL `evaluate` (`cakeml/pancake/semantics/panSemScript.sml:556`)
    returning a genuine `result option × state` pair.  The body extracts the
    total finite-support recursive evaluator `evalPanSemRecursiveCallHOLFinite`
    (its outer assembly marker is always `some`, so the assembly `Option` is
    dropped).  It is deliberately untagged: the body delegates through
    `toExact`, so it does not syntactically present HOL's clause-shaped body,
    and the delegating wrapper exposes only the Skip/Break/Continue equations
    uniformly, not the six recursive HOL clauses.  The faithful tagged port
    requires threading `memaddrsDecidable`/`shMemaddrsDecidable` through a
    finite eval context; tracked by `flapjack-6yq` (which blocks
    `flapjack-qj5`). -/
def evaluateHOLFiniteViaExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (PanSemResultExact width) × PanSemStateFiniteExact width σ
  | program =>
      match evalPanSemRecursiveCallHOLFinite state program with
      | some pair => pair
      | none => (none, state)

/-- Result bridge: the finite evaluator is exactly the `some` output of
    the total finite-support recursive evaluator, so it is the canonical
    finite-map rendering of HOL `evaluate` (Flapjack-specific, untagged). -/
theorem evaluateHOLFiniteViaExact_eq_some {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    evalPanSemRecursiveCallHOLFinite state program =
      some (evaluateHOLFiniteViaExact state program) := by
  obtain ⟨pair, hp⟩ := evalPanSemRecursiveCallHOLFinite_exists state program
  unfold evaluateHOLFiniteViaExact
  simp only [hp]

/-- Projection bridge: forgetting the finite support of the finite evaluator's
    post-state recovers the broad exact evaluator's output, transported along
    `toExact`. -/
theorem evaluateHOLFiniteViaExact_snd_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) :
    ∃ pair,
      evalPanSemRecursiveCallHOLFinite state program = some pair ∧
        evaluateHOLFiniteViaExact state program = pair ∧
          (Prod.snd (evaluateHOLFiniteViaExact state program)).toExact = pair.2.toExact := by
  obtain ⟨pair, hp⟩ := evalPanSemRecursiveCallHOLFinite_exists state program
  have heq : evaluateHOLFiniteViaExact state program = pair := by
    unfold evaluateHOLFiniteViaExact
    simp only [hp]
  exact ⟨pair, hp, heq, by rw [heq]⟩

/-- FLAPJACK-SPECIFIC evaluation context threading the decidability of the two
    address-domain predicates through the recursive finite evaluator.  Mirroring
    `PanSemExactEvalContext`, this is required because a recursive result state
    is opaque, so its `DecidablePred` instances cannot be reconstructed by
    computation.  Not a HOL declaration. -/
structure FiniteEvalContext (width : Nat) (σ : Type) [NeZero width] where
  state : PanSemStateFiniteExact width σ
  memaddrsDecidable : DecidablePred state.memaddrs
  shMemaddrsDecidable : DecidablePred state.shMemaddrs

namespace FiniteEvalContext

/-- Transport an evaluation context across a state whose two address-domain
    predicates are definitionally the same as the old state's. -/
def withState {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) : FiniteEvalContext width σ :=
  { state := state
    memaddrsDecidable := fun address => by rw [hmem]; exact context.memaddrsDecidable address
    shMemaddrsDecidable := fun address => by rw [hshared]; exact context.shMemaddrsDecidable address }

@[simp] theorem withState_state {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (state : PanSemStateFiniteExact width σ)
    (hmem : state.memaddrs = context.state.memaddrs)
    (hshared : state.shMemaddrs = context.state.shMemaddrs) :
    (withState context state hmem hshared).state = state := rfl

/-- Threading a context through its own state is the identity. -/
@[simp] theorem withState_self {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hmem : context.state.memaddrs = context.state.memaddrs)
    (hshared : context.state.shMemaddrs = context.state.shMemaddrs) :
    context.withState context.state hmem hshared = context := by
  cases context
  simp [FiniteEvalContext.withState]

end FiniteEvalContext

/-- The finite fix-clock never increases the clock. -/
theorem fixClockHOLFinite_clock_le {width : Nat} {σ : Type} [NeZero width] {β : Type}
    (oldState : PanSemStateFiniteExact width σ)
    (step : β × PanSemStateFiniteExact width σ) :
    (fixClockHOLFinite oldState step).2.clock ≤ oldState.clock := by
  change (if oldState.clock < step.2.clock then oldState.clock else step.2.clock) ≤
    oldState.clock
  split <;> omega

/-- FLAPJACK-SPECIFIC (not a HOL declaration): clause-for-clause finite-support
    rendering of the exact recursive program evaluator
    `evalPanSemRecursiveCallContextHOLExact`, returning a `FiniteEvalContext`
    so that the `memaddrs`/`shMemaddrs` deciders are threaded through recursive
    calls on updated finite states.  This is the prerequisite for the tagged
    `evaluate_def` port (bead `flapjack-6yq`). -/
def evalPanSemRecursiveCallFiniteContext {width : Nat} {σ : Type} [NeZero width] :
    ProgHOL width → FiniteEvalContext width σ →
      Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)
  | program, context => by
      let state := context.state
      letI : DecidablePred state.memaddrs := context.memaddrsDecidable
      letI : DecidablePred state.shMemaddrs := context.shMemaddrsDecidable
      exact match program with
      | .dec name shape initializer body =>
          match evalHOLFinite state initializer with
          | none => some (some .error, context)
          | some value =>
              if shapeEqHOL shape (shapeOfHOLExact value) then
                let bodyState := setVarHOLFinite name value state
                let bodyContext := context.withState bodyState rfl rfl
                match evalPanSemRecursiveCallFiniteContext body bodyContext with
                | none => none
                | some (result, postContext) =>
                    let restored := { postContext.state with
                      locals := HolFiniteMapExact.resVarEq postContext.state.locals
                        (name, state.locals.lookup name) }
                    some (result, postContext.withState restored rfl rfl)
              else some (some .error, context)
      | .seq first second =>
          match evalPanSemRecursiveCallFiniteContext first context with
          | none => none
          | some (firstResult, firstContext) =>
              let fixed := fixClockHOLFinite state (firstResult, firstContext.state)
              let fixedContext := firstContext.withState fixed.2 rfl rfl
              match firstResult with
              | none => evalPanSemRecursiveCallFiniteContext second fixedContext
              | some _ => some (firstResult, fixedContext)
      | .ite condition thenBranch elseBranch =>
          match evalHOLFinite state condition with
          | some (.val (.word value)) =>
              if value != 0 then
                evalPanSemRecursiveCallFiniteContext thenBranch context
              else
                evalPanSemRecursiveCallFiniteContext elseBranch context
          | _ => some (some .error, context)
      | .while condition body =>
          match evalHOLFinite state condition with
          | some (.val (.word word)) =>
              if word ≠ 0 then
                if state.clock = 0 then
                  some (some .timeOut,
                    context.withState (emptyLocalsHOLFinite state) rfl rfl)
                else
                  let entry := decClockHOLFinite state
                  let entryContext := context.withState entry rfl rfl
                  match evalPanSemRecursiveCallFiniteContext body entryContext with
                  | none => none
                  | some (bodyResult, bodyContext) =>
                      let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                      let fixedContext := bodyContext.withState fixed.2 rfl rfl
                      match bodyResult with
                      | some .continue | none =>
                          evalPanSemRecursiveCallFiniteContext
                            (.while condition body) fixedContext
                      | some .break => some (none, fixedContext)
                      | _ => some (bodyResult, fixedContext)
              else some (none, context)
          | _ => some (some .error, context)
      | .call info function arguments =>
          match evalListHOLFinite state arguments with
          | none => some (some .error, context)
          | some values =>
              match hlookup : lookupCodeHOLExact state.code.lookup function values with
              | none => some (some .error, context)
              | some (body, calleeLocals, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      context.withState (emptyLocalsHOLFinite state) rfl rfl)
                  else
                    let callee : HolFiniteMapExact MlS (ValueHOL width) :=
                      { lookup := calleeLocals, finiteSupport := lookupCodeHOLExact_calleeLocals_finiteSupport state.code.lookup function values body calleeLocals returnShape hlookup }
                    let entry : PanSemStateFiniteExact width σ := { state with clock := state.clock - 1, locals := callee }
                    let entryContext := context.withState entry rfl rfl
                    match evalPanSemRecursiveCallFiniteContext body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                        let fixedContext := bodyContext.withState fixed.2 rfl rfl
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) returnShape then
                              match info with
                              | none =>
                                  some (some (.returned value),
                                    fixedContext.withState
                                      (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
                              | some (none, _) =>
                                  some (none, fixedContext.withState
                                    { fixedContext.state with locals := state.locals } rfl rfl)
                              | some (some (kind, name), _) =>
                                  if isValidValueHOLExact state.toExact kind name value then
                                    some (none, fixedContext.withState
                                      (setKvarHOLFinite kind name value
                                        { fixedContext.state with locals := state.locals })
                                      (by cases kind <;> rfl) (by cases kind <;> rfl))
                                  else some (some .error, fixedContext)
                            else some (some .error, fixedContext)
                        | some (.exception exceptionId value) =>
                            match info with
                            | none =>
                                some (some (.exception exceptionId value),
                                  fixedContext.withState
                                    (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
                            | some (_, none) =>
                                some (some (.exception exceptionId value),
                                  fixedContext.withState
                                    (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
                            | some (_, some (handlerId, handlerVar, handlerProgram)) =>
                                if exceptionId = handlerId then
                                  match state.eshapes.lookup exceptionId with
                                  | some shape =>
                                      if shapeEqHOL (shapeOfHOLExact value) shape &&
                                          isValidValueHOLExact state.toExact .local handlerVar value then
                                        let handlerState := setVarHOLFinite handlerVar value
                                          { fixedContext.state with locals := state.locals }
                                        let handlerContext := fixedContext.withState
                                          handlerState rfl rfl
                                        evalPanSemRecursiveCallFiniteContext handlerProgram
                                          handlerContext
                                      else some (some .error, fixedContext)
                                  | none => some (some .error, fixedContext)
                                else
                                  some (some (.exception exceptionId value),
                                    fixedContext.withState
                                      (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
                        | some other =>
                            some (some other, fixedContext.withState
                              (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
      | .decCall resultName shape function arguments continuation =>
          match evalListHOLFinite state arguments with
          | none => some (some .error, context)
          | some values =>
              match hlookup : lookupCodeHOLExact state.code.lookup function values with
              | none => some (some .error, context)
              | some (body, calleeLocals, returnShape) =>
                  if state.clock = 0 then
                    some (some .timeOut,
                      context.withState (emptyLocalsHOLFinite state) rfl rfl)
                  else
                    let callee : HolFiniteMapExact MlS (ValueHOL width) :=
                      { lookup := calleeLocals, finiteSupport := lookupCodeHOLExact_calleeLocals_finiteSupport state.code.lookup function values body calleeLocals returnShape hlookup }
                    let entry : PanSemStateFiniteExact width σ := { state with clock := state.clock - 1, locals := callee }
                    let entryContext := context.withState entry rfl rfl
                    match evalPanSemRecursiveCallFiniteContext body entryContext with
                    | none => none
                    | some (bodyResult, bodyContext) =>
                        let fixed := fixClockHOLFinite entry (bodyResult, bodyContext.state)
                        let fixedContext := bodyContext.withState fixed.2 rfl rfl
                        match bodyResult with
                        | none => some (some .error, fixedContext)
                        | some .break => some (some .error, fixedContext)
                        | some .continue => some (some .error, fixedContext)
                        | some (.returned value) =>
                            if shapeEqHOL (shapeOfHOLExact value) shape &&
                                shapeEqHOL (shapeOfHOLExact value) returnShape then
                              let continuationState := setVarHOLFinite resultName value
                                { fixedContext.state with locals := state.locals }
                              let continuationContext := fixedContext.withState
                                continuationState rfl rfl
                              match evalPanSemRecursiveCallFiniteContext continuation
                                  continuationContext with
                              | none => none
                              | some (continuationResult, continuationPost) =>
                                  let restored := { continuationPost.state with
                                    locals := HolFiniteMapExact.resVarEq
                                      continuationPost.state.locals
                                      (resultName, state.locals.lookup resultName) }
                                  some (continuationResult,
                                    continuationPost.withState restored rfl rfl)
                            else some (some .error, fixedContext)
                        | some other =>
                            some (some other, fixedContext.withState
                              (emptyLocalsHOLFinite fixedContext.state) rfl rfl)
      | .skip => some (none, context)
      | .break => some (some .break, context)
      | .continue => some (some .continue, context)
      | .annot _ _ => some (none, context)
      | other =>
          match hres : evalPanSemNonrecursiveHOLFinite state other with
          | none => none
          | some pair =>
              some (pair.1, context.withState pair.2
                (evalPanSemNonrecursiveHOLFinite_memaddrs state other pair hres)
                (evalPanSemNonrecursiveHOLFinite_shMemaddrs state other pair hres))
termination_by _program context => (context.state.clock, sizeOf _program)
decreasing_by
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [FiniteEvalContext.withState]
    by_cases hlt : fixed.2.clock < state.clock
    · apply Prod.Lex.left
      exact hlt
    · have hle : fixed.2.clock ≤ state.clock :=
        fixClockHOLFinite_clock_le state (firstResult, firstContext.state)
      have heq : fixed.2.clock = state.clock := by omega
      rw [heq]
      apply Prod.Lex.right
      simp_wf
      omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.right
    simp_wf
    omega
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [FiniteEvalContext.withState, setVarHOLFinite]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))
  · simp only [FiniteEvalContext.withState]
    apply Prod.Lex.left
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide)
  · simp only [FiniteEvalContext.withState, setVarHOLFinite]
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (fixClockHOLFinite_clock_le entry (bodyResult, bodyContext.state))
      (Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by decide))

/-- FLAPJACK-SPECIFIC (no `@[hol]` tag): the clause-for-clause finite context
    evaluator is total.  Its outer `Option` is only the recursive-case assembly
    marker, so it is always `some`; this is the finite-context analogue of
    `evalPanSemRecursiveCallContextHOLExact_total`. -/
theorem evalPanSemRecursiveCallFiniteContext_total {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    ∃ output, evalPanSemRecursiveCallFiniteContext program context = some output := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context <;> simp_all
  case case53 =>
    rename_i inst context state other h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 hres
    cases other <;> simp_all [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
    · exact h9 _ _ _ _ rfl rfl rfl rfl
    · exact h4 _ _ _ _ _ rfl rfl rfl rfl rfl

/-- FLAPJACK-SPECIFIC provisional projection (not a HOL declaration; carries no
    `@[hol]` tag): the state-level view of the clause-for-clause finite context
    evaluator `evalPanSemRecursiveCallFiniteContext`.

    As with the broad exact evaluator `evalPanSemRecursiveCallContextHOLExact`,
    the outer `Option` is the *assembly marker* for the recursive cases (it is
    `none` only on the not-yet-assembled internal branches), not part of HOL
    `evaluate_def`'s `result option × state` result.  The marker is provably
    inert (`evaluateHOLFinite_ne_none`), but the equivalence with the broad exact
    evaluator is still pending (bead `flapjack-6yq`), so this wrapper deliberately
    keeps the marker rather than totalizing an unreachable `none` branch to
    `(none, state)` (which would be observationally wrong).

    Exposed clause-by-clause in
    `Flapjack.Pancake.Semantics.PanSem.EvaluateFinite`. -/
def evaluateHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    ProgHOL width →
      Option (Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :=
  fun program =>
    (evalPanSemRecursiveCallFiniteContext program ⟨state, h, hshared⟩).map
      (fun pair => (pair.1, pair.2.state))

/-- FLAPJACK-SPECIFIC (no `@[hol]` tag): the state-level projection never hits the
    assembly marker's `none`, by `evalPanSemRecursiveCallFiniteContext_total`. -/
theorem evaluateHOLFinite_ne_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width) : evaluateHOLFinite state program ≠ none := by
  obtain ⟨output, houtput⟩ :=
    evalPanSemRecursiveCallFiniteContext_total program (⟨state, h, hshared⟩ : FiniteEvalContext width σ)
  unfold evaluateHOLFinite
  rw [houtput]
  simp

end PanSemStateFiniteExact

end Flapjack
