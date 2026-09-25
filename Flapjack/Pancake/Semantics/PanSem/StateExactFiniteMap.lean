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

  Five helper definitions have passed their case-by-case review and carry
  `@[hol ...]` with that qualifier: `decClockHOLFinite` (`dec_clock_def`),
  `fixClockHOLFinite` (`fix_clock_def`), `lookupKvarHOLFinite` (`lookup_kvar_def`),
  `emptyLocalsHOLFinite` (`empty_locals_def`) and `setKvarHOLFinite`
  (`set_kvar_def`).  `setKvarHOLFinite` routes through the untagged canonical-
  update wrappers `setVarHOLFinite`/`setGlobalHOLFinite`, which use
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

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL StructContextExact ProgHOL ExpHOL)

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
    carrier.  Untagged canonical-update wrapper used by the tagged
    `setKvarHOLFinite`; the carrier's map fields are recorded there by the
    `fmap_as_finite_support` qualifier. -/
def setVarHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (value : ValueHOL width) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with locals := state.locals.update (name, value) }

/-- HOL `set_global_def` (`cakeml/pancake/semantics/panSemScript.sml:403-406`):
    `set_global v value s = s with globals := s.globals |+ (v,value)`, i.e. the
    canonical `HolFiniteMapExact.update` on the `globals` component. -/
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

end PanSemStateFiniteExact

end Flapjack
