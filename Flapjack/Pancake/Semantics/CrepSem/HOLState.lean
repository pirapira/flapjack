import Flapjack.FiniteMap.Basic
import Flapjack.Basis.Pure.MlString
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.FfiHOL

/-!
# HOL-shaped state carriers for Crep expression proofs

This file records the field carriers from `crepSem$state` independently of
the executable runtime adapter. Its finite maps carry an explicit finite
support witness, code names use `MlString`, code entries use `CrepProgHOL`,
and memory domains are Lean sets. The word dimension is represented by the
canonical `BitVec width` model for each positive HOL dimension.

These declarations are Flapjack representation infrastructure and carry no
`@[hol]` tags: the word index is represented by its positive cardinality and
`BitVec width`, rather than by an arbitrary HOL `finite_index` type together
with an explicit carrier equivalence. The expression-evaluator projection
below also deliberately forgets `code` and `ffi`, which expression `eval`
does not read. It maps only the expression-observable fields into the
all-width source evaluator state. This is a state-carrier prerequisite, not a
port of the evaluator itself.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Flapjack finite-support map infrastructure: a total lookup function with a
proof that its defined domain is finite. This models HOL `fmap` observations
but is not separately tagged as the generic finite-map type declaration. -/
structure HolFiniteMapExact (α β : Type) where
  lookup : α → Option β
  finiteSupport : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

namespace HolFiniteMapExact

/-- Flapjack encoding of HOL `FMAP_MAP2`: preserve keys and map each present
value with the key available to the callback. -/
def map2 (f : α × β → γ) (map : HolFiniteMapExact α β) :
    HolFiniteMapExact α γ where
  lookup key := (map.lookup key).map (fun value => f (key, value))
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hlookup
    apply hkeys key
    cases hsource : map.lookup key <;> simp [hsource] at hlookup ⊢

@[simp] theorem lookup_map2 (f : α × β → γ)
    (map : HolFiniteMapExact α β) (key : α) :
    (map.map2 f).lookup key = (map.lookup key).map (fun value => f (key, value)) := rfl

/-- HOL `FEMPTY` on the finite-support carrier: the everywhere-undefined map.
    Its support witness is the empty key list. -/
def empty : HolFiniteMapExact α β where
  lookup _ := none
  finiteSupport := ⟨[], by intro key h; exact absurd rfl h⟩

/-- HOL `FUPDATE` (`|+`) on the finite-support carrier: the updated key is added
    to the support list, so the result keeps an explicit finite support. -/
def update [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β) (entry : α × β) :
    HolFiniteMapExact α β where
  lookup := FUPDATE map.lookup entry
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨entry.1 :: keys, ?_⟩
    intro key hlookup
    by_cases h : entry.1 == key
    · have hk : entry.1 = key := beq_iff_eq.mp h
      subst hk
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply hkeys
      simpa [FUPDATE, h] using hlookup

/-- HOL `FUPDATE_LIST` (`|++`) on the finite-support carrier, matching the raw
    finite-map `FUPDATE_LIST` (`foldl FUPDATE`). Each update adds its key to the
    support, so the result is finite-support by construction. -/
def updateList [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) : HolFiniteMapExact α β where
  lookup := FUPDATE_LIST map.lookup entries
  finiteSupport := by
    induction entries generalizing map with
    | nil => simpa [FUPDATE_LIST] using map.finiteSupport
    | cons entry entries ih =>
      simpa [FUPDATE_LIST_cons, update] using ih (update map entry)

/-- HOL domain subtraction (`\\`) on the finite-support carrier: removing a key
    can only shrink the support, so the original witness still covers it. -/
def erase [BEq α] (map : HolFiniteMapExact α β) (key : α) :
    HolFiniteMapExact α β where
  lookup := FDOMSUB map.lookup key
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro k hk
    apply hkeys k
    by_cases h : key == k
    · simp [FDOMSUB, h] at hk
    · simpa [FDOMSUB, h] using hk

/-- HOL `res_var` on the finite-support carrier (`crepSemScript.sml:163`):
    `NONE` subtracts the key from the domain, `SOME v` updates it. -/
def resVar [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β)
    (entry : α × Option β) : HolFiniteMapExact α β :=
  match entry.2 with
  | none => erase map entry.1
  | some value => update map (entry.1, value)

/-- HOL-equality (`=`) `FUPDATE` on the finite-support carrier, using
    `DecidableEq` (Lean's encoding of HOL `=`) rather than Boolean `BEq`. -/
def updateEq [DecidableEq α] (map : HolFiniteMapExact α β) (entry : α × β) :
    HolFiniteMapExact α β where
  lookup := FUPDATE_HOL map.lookup entry
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨entry.1 :: keys, ?_⟩
    intro key hlookup
    simp only [FUPDATE_HOL] at hlookup
    by_cases h : key = entry.1
    · subst h
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply hkeys
      simpa [h] using hlookup

/-- HOL `FUPDATE_LIST` (`|++`) on the finite-support carrier using `DecidableEq`
    (HOL `=`), mirroring `updateList` with the equality-based `FUPDATE_HOL`. -/
def updateListEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) : HolFiniteMapExact α β where
  lookup := FUPDATE_LIST_HOL map.lookup entries
  finiteSupport := by
    induction entries generalizing map with
    | nil => simpa [FUPDATE_LIST_HOL] using map.finiteSupport
    | cons entry entries ih =>
      simpa [FUPDATE_LIST_HOL_cons, updateEq] using ih (updateEq map entry)

/-- HOL-equality (`=`) domain subtraction on the finite-support carrier. -/
def eraseEq [DecidableEq α] (map : HolFiniteMapExact α β) (key : α) :
    HolFiniteMapExact α β where
  lookup := FDOMSUB_HOL map.lookup key
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := map.finiteSupport
    refine ⟨keys, ?_⟩
    intro k hk
    apply hkeys k
    by_cases h : k = key
    · simp [FDOMSUB_HOL, h] at hk
    · simpa [FDOMSUB_HOL, h] using hk

/-- HOL-equality port of `crepSem$res_var` (`crepSemScript.sml:163`) on the
    finite-support carrier: `NONE` subtracts the key from the domain, `SOME v`
    updates it. Uses `DecidableEq` (HOL `=`) so HOL's polymorphic key type is
    preserved with no `BEq`/`LawfulBEq` side conditions. Untagged: the carrier
    is `HolFiniteMapExact` itself (no owning structure field), so the
    `fmap_as_finite_support` qualifier does not directly apply; the exact
    tagging route is tracked by `flapjack-pxn.18.3.7.1.3.1.1.2.4`. -/
def resVarEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (entry : α × Option β) : HolFiniteMapExact α β :=
  match entry.2 with
  | none => eraseEq map entry.1
  | some value => updateEq map (entry.1, value)

@[simp] theorem lookup_empty (key : α) :
    (empty : HolFiniteMapExact α β).lookup key = none := rfl

@[simp] theorem lookup_update [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β) (entry : α × β)
    (key : α) :
    (update map entry).lookup key = FUPDATE map.lookup entry key := rfl

@[simp] theorem lookup_updateList [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) (key : α) :
    (updateList map entries).lookup key = FUPDATE_LIST map.lookup entries key := rfl

@[simp] theorem lookup_updateListEq [DecidableEq α] (map : HolFiniteMapExact α β)
    (entries : List (α × β)) (key : α) :
    (updateListEq map entries).lookup key = FUPDATE_LIST_HOL map.lookup entries key := rfl

@[simp] theorem lookup_erase [BEq α] (map : HolFiniteMapExact α β) (key k : α) :
    (erase map key).lookup k = FDOMSUB map.lookup key k := rfl

@[simp] theorem lookup_resVar_none [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β) (key : α) :
    (resVar map (key, none)).lookup = FDOMSUB map.lookup key := rfl

@[simp] theorem lookup_resVar_some [BEq α] [LawfulBEq α] (map : HolFiniteMapExact α β) (key : α)
    (value : β) :
    (resVar map (key, some value)).lookup = FUPDATE map.lookup (key, value) := rfl

@[simp] theorem lookup_updateEq [DecidableEq α] (map : HolFiniteMapExact α β) (entry : α × β)
    (key : α) :
    (updateEq map entry).lookup key = FUPDATE_HOL map.lookup entry key := rfl

@[simp] theorem lookup_eraseEq [DecidableEq α] (map : HolFiniteMapExact α β) (key k : α) :
    (eraseEq map key).lookup k = FDOMSUB_HOL map.lookup key k := rfl

@[simp] theorem lookup_resVarEq_none [DecidableEq α] (map : HolFiniteMapExact α β) (key : α) :
    (resVarEq map (key, none)).lookup = FDOMSUB_HOL map.lookup key := rfl

@[simp] theorem lookup_resVarEq_some [DecidableEq α] (map : HolFiniteMapExact α β) (key : α)
    (value : β) :
    (resVarEq map (key, some value)).lookup = FUPDATE_HOL map.lookup (key, value) := rfl

end HolFiniteMapExact

/-- Flapjack's HOL-shaped encoding of `crepSem$state`
(`crepSemScript.sml:19-32`): finite maps for locals/globals/code, a total
word-to-word_lab memory function, set-valued memory domains, clock/endian
fields, an exact `HolFfiState σ`, and base/top words. It is untagged because its
word index is represented by positive `width`/`BitVec width`; the explicit
equivalence to each arbitrary HOL `finite_index` instance is not carried here. -/
structure CrepSemHOLState (width : Nat) [NeZero width] (ffiState : Type) where
  locals : HolFiniteMapExact Nat (HolWordLab width)
  globals : HolFiniteMapExact (BitVec 5) (HolWordLab width)
  code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState ffiState
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Broad (unrestricted) counterpart of `CrepSemHOLState`: the three map fields
are plain lookup functions, a strict superset of HOL's finite maps. It exists
only to state the canonical finite-map translation witness
`holFmapAsFiniteSupportWitness`; `FiniteSupport` cuts out the HOL-image
subcarrier. -/
structure CrepSemBroadState (width : Nat) [NeZero width] (ffiState : Type) where
  locals : Nat → Option (HolWordLab width)
  globals : BitVec 5 → Option (HolWordLab width)
  code : MlString → Option (List Nat × CrepProgHOL width)
  memory : BitVec width → HolWordLab width
  memaddrs : BitVec width → Prop
  shMemaddrs : BitVec width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState ffiState
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Field-wise finite support of `CrepSemBroadState`, matching HOL's `|->`
fields. -/
def CrepSemBroadState.FiniteSupport {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemBroadState width ffiState) : Prop :=
  (∃ keys : List Nat, ∀ key, state.locals key ≠ none → key ∈ keys) ∧
  (∃ keys : List (BitVec 5), ∀ key, state.globals key ≠ none → key ∈ keys) ∧
  (∃ keys : List MlString, ∀ key, state.code key ≠ none → key ∈ keys)

/-- Forget the finite-support witnesses, reading every map through `.lookup`. -/
def CrepSemHOLState.toBroad {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) : CrepSemBroadState width ffiState where
  locals := state.locals.lookup
  globals := state.globals.lookup
  code := state.code.lookup
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- The projection lands in the finite-support subtype. -/
theorem CrepSemHOLState.toBroad_finiteSupport {width : Nat} [NeZero width]
    {ffiState : Type} (state : CrepSemHOLState width ffiState) :
    state.toBroad.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport, state.code.finiteSupport⟩

/-- Rebuild the finite-map carrier from a broad state together with a
finite-support proof; the inverse of `toBroad` on the finite-support subtype. -/
def CrepSemBroadState.ofBroad {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport) :
    CrepSemHOLState width ffiState where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  code := { lookup := state.code, finiteSupport := h.2.2 }
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- `toBroad` after `ofBroad` is the identity on a finite-support broad state. -/
theorem CrepSemBroadState.toBroad_ofBroad {width : Nat} [NeZero width]
    {ffiState : Type} (state : CrepSemBroadState width ffiState)
    (h : state.FiniteSupport) : (ofBroad state h).toBroad = state := rfl

/-- `ofBroad` after `toBroad` is the identity on the finite-map carrier. -/
theorem CrepSemBroadState.ofBroad_toBroad {width : Nat} [NeZero width]
    {ffiState : Type} (state : CrepSemHOLState width ffiState) :
    ofBroad state.toBroad state.toBroad_finiteSupport = state := by
  cases state
  rfl

namespace CrepSemHOLState

/-- Canonical kernel witness for the `fmap_as_finite_support` `@[hol]`
qualifier on `CrepSemHOLState`: the finite-map carrier is invertibly related
to the broad one. Extensionality is the separate `HolFiniteMapExact.ext`
theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {ffiState : Type} :
    (∀ (state : CrepSemBroadState width ffiState) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width ffiState,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  ⟨fun state h => CrepSemBroadState.toBroad_ofBroad state h,
    fun state => CrepSemBroadState.ofBroad_toBroad state⟩

end CrepSemHOLState

/-- Arbitrary-index HOL-shaped expression state for polymorphic evaluator
support. The word index is abstract as `ι`, with words represented by
`ι → Bool`; evaluator proofs supply a `HolFiniteDimension ι` dictionary.
The code-entry type is opaque because expression evaluation never reads code,
while HOL `mapc` can still update the finite map exactly with `map2`.

This is Flapjack infrastructure rather than an exact `crepSem$state` port:
generic `CrepProg` does not yet preserve HOL's program/name carriers, and the
evaluator projection below fixes the unobserved FFI field and uses the
explicit word-dimension adapter. Do not attach a HOL tag to theorems over this
carrier until those representation relations are proved. -/
structure CrepSemHOLFiniteState (ι : Type) (codeEntry ffiState : Type) where
  locals : HolFiniteMapExact Nat (PanWordLab (ι → Bool))
  globals : HolFiniteMapExact (BitVec 5) (PanWordLab (ι → Bool))
  code : HolFiniteMapExact MlString codeEntry
  memory : (ι → Bool) → PanWordLab (ι → Bool)
  memaddrs : (ι → Bool) → Prop
  shMemaddrs : (ι → Bool) → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState ffiState
  baseAddr : ι → Bool
  topAddr : ι → Bool

private def crepExpressionProjectionFfi : FfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    state := ()
    ioEvents := [] }

private def holWordLabToBits {width : Nat} (cell : HolWordLab width) :
    PanWordLab (Fin width → Bool) :=
  match cell with
  | .word word => .word (bitVecToHolWordBits word)

/-- Flapjack representation helper exposing the exact-state word-cell
projection for carrier-bridge proofs; it has no HOL theorem of its own. -/
@[simp] theorem holWordLabToBits_word {width : Nat} (word : BitVec width) :
    holWordLabToBits (HolWordLab.word word) =
      PanWordLab.word (bitVecToHolWordBits word) := rfl

/-- Project just the observable fields to the existing all-width source
evaluator. Code is empty and FFI is a fixed witness because expression `eval`
does not inspect either field; memory domains are converted from HOL sets to
their Boolean characteristic functions. -/
noncomputable def CrepSemHOLState.toExpressionEvaluatorState
    {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) :
    CrepHolState (Fin width → Bool) Unit := by
  classical
  exact
    { locals := fun name => (state.locals.lookup name).map holWordLabToBits
      globals := fun name => (state.globals.lookup name).map holWordLabToBits
      code := fun _ => none
      memory := fun address => holWordLabToBits
        (state.memory (holWordBitsToBitVec address))
      memaddrs := fun address => decide
        (state.memaddrs (holWordBitsToBitVec address))
      shMemaddrs := fun address => decide
        (state.shMemaddrs (holWordBitsToBitVec address))
      clock := state.clock
      bigEndian := state.be
      ffi := crepExpressionProjectionFfi
      baseAddress := bitVecToHolWordBits state.baseAddr
      topAddress := bitVecToHolWordBits state.topAddr }

/-- Project the expression-observable state fields directly to the canonical
BitVec word evaluator. Code and FFI use fixed witnesses because expression
evaluation does not inspect either field. Unlike
`toExpressionEvaluatorState`, this view does not pass through `Fin width →
Bool` before returning to the production RISC-V `BitVec width` carrier. -/
noncomputable def CrepSemHOLState.toBitVecEvaluatorState
    {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) :
    CrepHolState (RiscV.Word width) Unit := by
  classical
  exact
    { locals := fun name => (state.locals.lookup name).map HolWordLab.toPanWordLab
      globals := fun name => (state.globals.lookup name).map HolWordLab.toPanWordLab
      code := fun _ => none
      memory := fun address => (state.memory address).toPanWordLab
      memaddrs := fun address => decide (state.memaddrs address)
      shMemaddrs := fun address => decide (state.shMemaddrs address)
      clock := state.clock
      bigEndian := state.be
      ffi := crepExpressionProjectionFfi
      baseAddress := state.baseAddr
      topAddress := state.topAddr }

/-! ## Exact finite-support state updates

HOL `crepSem$set_var_def` / `set_globals_def` / `upd_locals_def` /
`empty_locals_def` (`crepSemScript.sml:55,61,66,71`) act on the finite-map
fields of `crepSem$state`. The state helpers below restate them over
`CrepSemHOLState`, whose locals/globals/code fields are finite maps by type
(`HolFiniteMapExact`), so each update is finite-support by construction; this is
why the raw-map state tags withdrawn in `flapjack-pxn.18.3.7.1.3.1.1.3` can be
restored here. The positive `BitVec width` word index is the accepted canonical
model for HOL's positive `dimindex` (the same representation as the
`reviewed_exact` `ProgHOL`/`ValueHOL`/`HolWordLab` and the `PanSem/memLoadHOLExact`
port). `upd_locals`'s `updateList`, and the Nat-keyed `FUPDATE`, agree with HOL
`|++`/`|+` because Nat's `BEq` is lawful (`beq_iff_eq`). The kernel-checked
bridges connect each update to the executable `CrepHolState` helper through the
projection `toBitVecEvaluatorState`.

These helpers are **temporarily untagged**: their finite-map representation must
be recorded with the `@[hol]` qualifier `(fmap_as_finite_support := [locals,
globals, code])` rather than a bare tag, per the standard-translation rule. That
qualifier, its canonical witness `holFmapAsFiniteSupportWitness`, and the
`reviewed_fmap_as_finite_support` manifest status are being added under bead
`flapjack-pxn.18.3.7.1.3.1.1.2.4` (ds3 commits `01dae7ba5`/`bcca041b5`, not yet
in the integration branch). Each helper is still reviewed case-by-case for
statement/side conditions and will be re-tagged with the qualifier only once the
checker accepts it; no exact claim is made here until then.

HOL `crepSem$res_var_def` (`crepSemScript.sml:163`) is *polymorphic in the key
type*, so it is ported as the generic `HolFiniteMapExact.resVarEq`
(`[DecidableEq α]`, HOL `=`) above. Its carrier is `HolFiniteMapExact` itself,
so the field-based `fmap_as_finite_support` qualifier does not directly apply;
the exact tagging route is part of the same follow-up bead. The state-local
`CrepSemHOLState.resVar` below is a Nat-fixed, `BEq`-based convenience wrapper
kept for the `resVarW` bridge and carries no tag. -/

namespace HolFiniteMapExact

/-- Pointwise `Option.map` commutes with a single finite-map update. -/
theorem map_update_eq [BEq α] (f : β → γ) (base : FiniteMap α β)
    (entry : α × β) (key : α) :
    (FUPDATE base entry key).map f =
      FUPDATE (fun k => (base k).map f) (entry.1, f entry.2) key := by
  by_cases h : entry.1 == key <;> simp [FUPDATE, h]

/-- Pointwise `Option.map` commutes with `FUPDATE_LIST`, adding the mapped
    entries in the same order. -/
theorem map_updateList_eq [BEq α] (f : β → γ) (base : FiniteMap α β)
    (entries : List (α × β)) (key : α) :
    (FUPDATE_LIST base entries key).map f =
      FUPDATE_LIST (fun k => (base k).map f)
        (entries.map (fun entry => (entry.1, f entry.2))) key := by
  induction entries generalizing base with
  | nil => rfl
  | cons entry entries ih =>
    simp only [FUPDATE_LIST_cons]
    rw [ih (FUPDATE base entry)]
    simp only [map_update_eq f base entry, FUPDATE_LIST_cons, List.map_cons]

end HolFiniteMapExact

/-- Flapjack-only record extensionality for the evaluator-state carrier, used to
    state the finite-support projection bridges field by field. -/
private theorem crepHolState_eq_of_fields {α σ : Type}
    {left right : CrepHolState α σ}
    (hLocals : left.locals = right.locals)
    (hGlobals : left.globals = right.globals)
    (hCode : left.code = right.code)
    (hMemory : left.memory = right.memory)
    (hMemaddrs : left.memaddrs = right.memaddrs)
    (hShMemaddrs : left.shMemaddrs = right.shMemaddrs)
    (hClock : left.clock = right.clock)
    (hBigEndian : left.bigEndian = right.bigEndian)
    (hFfi : left.ffi = right.ffi)
    (hBaseAddress : left.baseAddress = right.baseAddress)
    (hTopAddress : left.topAddress = right.topAddress) :
    left = right := by
  cases left
  cases right
  simp_all

namespace CrepSemHOLState

/-- HOL `set_var` (`crepSemScript.sml:55-57`) over the exact finite-support
    carrier. The `(fmap_as_finite_support := [locals, globals, code])` qualifier
    records that the HOL state's finite maps are represented by
    `HolFiniteMapExact`; the body uses HOL equality (`=`). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "set_var_def" (fmap_as_finite_support := [locals, globals, code])]
def setVar {width : Nat} [NeZero width] {ffiState : Type} (name : Nat)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    CrepSemHOLState width ffiState :=
  { state with locals := state.locals.updateEq (name, value) }

/-- HOL `set_globals` (`crepSemScript.sml:61-63`) over the exact finite-support
    carrier, using HOL equality (`=`). -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "set_globals_def" (fmap_as_finite_support := [locals, globals, code])]
def setGlobals {width : Nat} [NeZero width] {ffiState : Type} (key : BitVec 5)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    CrepSemHOLState width ffiState :=
  { state with globals := state.globals.updateEq (key, value) }

/-- HOL `upd_locals` (`crepSemScript.sml:66-68`) over the exact finite-support
    carrier: locals are replaced by `FEMPTY |++ varargs`, using HOL equality. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "upd_locals_def" (fmap_as_finite_support := [locals, globals, code])]
def updLocals {width : Nat} [NeZero width] {ffiState : Type}
    (varargs : List (Nat × HolWordLab width))
    (state : CrepSemHOLState width ffiState) : CrepSemHOLState width ffiState :=
  { state with locals := HolFiniteMapExact.empty.updateListEq varargs }

/-- HOL `empty_locals` (`crepSemScript.sml:71-74`) over the exact finite-support
    carrier, using `FEMPTY` for locals. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "empty_locals_def" (fmap_as_finite_support := [locals, globals, code])]
def emptyLocals {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) : CrepSemHOLState width ffiState :=
  { state with locals := HolFiniteMapExact.empty }

/-- Flapjack-specific Nat-fixed, `BEq`-based convenience wrapper around the
    generic `HolFiniteMapExact.resVarEq`, kept only to connect the executable
    `resVarW`. It carries no `@[hol]` tag: HOL `res_var_def` is polymorphic in
    the key type and the exact tagging route is tracked by
    `flapjack-pxn.18.3.7.1.3.1.1.2.4`. -/
def resVar {width : Nat} [NeZero width]
    (map : HolFiniteMapExact Nat (HolWordLab width))
    (entry : Nat × Option (HolWordLab width)) :
    HolFiniteMapExact Nat (HolWordLab width) :=
  map.resVar entry

/-- Kernel-checked bridge: the finite-support `set_var` helper projects to the
    executable `setCrepHolVarW` under `toBitVecEvaluatorState`. -/
theorem toBitVecEvaluatorState_setVar {width : Nat} [NeZero width]
    {ffiState : Type} (name : Nat) (value : HolWordLab width)
    (state : CrepSemHOLState width ffiState) :
    (setVar name value state).toBitVecEvaluatorState =
      setCrepHolVarW name value.toPanWordLab state.toBitVecEvaluatorState := by
  unfold setVar setCrepHolVarW
  dsimp only [toBitVecEvaluatorState]
  refine crepHolState_eq_of_fields ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL_eq_FUPDATE]
  exact HolFiniteMapExact.map_update_eq HolWordLab.toPanWordLab state.locals.lookup
    (name, value) key

/-- Kernel-checked bridge: the finite-support `set_globals` helper projects to
    the executable `setCrepHolGlobalsW` under `toBitVecEvaluatorState`. -/
theorem toBitVecEvaluatorState_setGlobals {width : Nat} [NeZero width]
    {ffiState : Type} (key : BitVec 5) (value : HolWordLab width)
    (state : CrepSemHOLState width ffiState) :
    (setGlobals key value state).toBitVecEvaluatorState =
      setCrepHolGlobalsW key value.toPanWordLab state.toBitVecEvaluatorState := by
  unfold setGlobals setCrepHolGlobalsW
  dsimp only [toBitVecEvaluatorState]
  refine crepHolState_eq_of_fields rfl ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
  funext k
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL_eq_FUPDATE]
  exact HolFiniteMapExact.map_update_eq HolWordLab.toPanWordLab state.globals.lookup
    (key, value) k

/-- Kernel-checked bridge: the finite-support `upd_locals` helper projects to
    the executable `updCrepHolLocalsW` under `toBitVecEvaluatorState`. -/
theorem toBitVecEvaluatorState_updLocals {width : Nat} [NeZero width]
    {ffiState : Type} (varargs : List (Nat × HolWordLab width))
    (state : CrepSemHOLState width ffiState) :
    (updLocals varargs state).toBitVecEvaluatorState =
      updCrepHolLocalsW
        (varargs.map (fun entry => (entry.1, entry.2.toPanWordLab)))
        state.toBitVecEvaluatorState := by
  unfold updLocals updCrepHolLocalsW
  dsimp only [toBitVecEvaluatorState]
  refine crepHolState_eq_of_fields ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  funext key
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  exact HolFiniteMapExact.map_updateList_eq HolWordLab.toPanWordLab
    HolFiniteMapExact.empty.lookup varargs key

/-- Kernel-checked bridge: the finite-support `empty_locals` helper projects to
    the executable `emptyCrepHolLocalsW` under `toBitVecEvaluatorState`. -/
theorem toBitVecEvaluatorState_emptyLocals {width : Nat} [NeZero width]
    {ffiState : Type} (state : CrepSemHOLState width ffiState) :
    (emptyLocals state).toBitVecEvaluatorState =
      emptyCrepHolLocalsW state.toBitVecEvaluatorState := by
  unfold emptyLocals emptyCrepHolLocalsW
  dsimp only [toBitVecEvaluatorState]
  refine crepHolState_eq_of_fields ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  funext key
  rfl

/-- Kernel-checked bridge: the finite-support `res_var` lookup is the
    executable `resVarW` lookup after applying the `HolWordLab` projection. -/
theorem lookup_resVarW {width : Nat} [NeZero width]
    (map : HolFiniteMapExact Nat (HolWordLab width)) (key : Nat)
    (value : Option (HolWordLab width)) :
    (fun k => ((resVar map (key, value)).lookup k).map HolWordLab.toPanWordLab) =
      resVarW (fun k => (map.lookup k).map HolWordLab.toPanWordLab)
        (key, value.map HolWordLab.toPanWordLab) := by
  cases value with
  | none =>
    funext k
    by_cases h : key = k <;>
      simp [CrepSemHOLState.resVar, HolFiniteMapExact.resVar,
        HolFiniteMapExact.erase, resVarW, Flapjack.resVar, FDOMSUB, h]
  | some value =>
    funext k
    by_cases h : key = k <;>
      simp [CrepSemHOLState.resVar, HolFiniteMapExact.resVar,
        HolFiniteMapExact.update, resVarW, Flapjack.resVar, FUPDATE, h]

end CrepSemHOLState

/-- Port of HOL `dec_clock_def` (`crepSemScript.sml:145-148`) over the
    finite-support `CrepSemHOLState` carrier, in the same module as the owning
    structure and its canonical `holFmapAsFiniteSupportWitness`. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "dec_clock_def" (fmap_as_finite_support := [locals, globals, code])]
def decClockCrepSemHOL {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  { state with clock := state.clock - 1 }

/-- Port of HOL `fix_clock_def` (`crepSemScript.sml:150-152`) over the
    finite-support `CrepSemHOLState` carrier. The result is polymorphic in the
    unconstrained `res` component, as in HOL. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "fix_clock_def" (fmap_as_finite_support := [locals, globals, code])]
def fixClockCrepSemHOL {width : Nat} [NeZero width] {σ : Type} {β : Type}
    (oldState : CrepSemHOLState width σ) (step : β × CrepSemHOLState width σ) :
    β × CrepSemHOLState width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-- Port of HOL `fix_clock_IMP_LESS_EQ` (`crepSemScript.sml:155-158`):
    `fix_clock` never increases the clock. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "fix_clock_IMP_LESS_EQ" (fmap_as_finite_support := [locals, globals, code])]
theorem fixClockCrepSemHOL_IMP_LESS_EQ {width : Nat} [NeZero width] {σ : Type}
    {β : Type} (state : CrepSemHOLState width σ) (x : β × CrepSemHOLState width σ)
    (res : β) (s1 : CrepSemHOLState width σ)
    (h : fixClockCrepSemHOL state x = (res, s1)) : s1.clock ≤ state.clock := by
  obtain ⟨value, stepState⟩ := x
  simp only [fixClockCrepSemHOL, Prod.mk.injEq] at h
  obtain ⟨_, hstate⟩ := h
  subst hstate
  change (if state.clock < stepState.clock then state.clock else stepState.clock) ≤
    state.clock
  split <;> omega

/-- Port of HOL `mem_load_def` (`crepSemScript.sml:48-51`) over the
    finite-support `CrepSemHOLState` carrier: a total `word → word_lab` memory
    guarded by the `memaddrs` set. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "mem_load_def" (fmap_as_finite_support := [locals, globals, code])]
def memLoadCrepSemHOL {width : Nat} [NeZero width] {σ : Type}
    (address : BitVec width) (state : CrepSemHOLState width σ)
    [DecidablePred state.memaddrs] :
    Option (HolWordLab width) :=
  if state.memaddrs address then some (state.memory address) else none

/-- Project expression-observable fields of the arbitrary-index state to the
existing source evaluator. Code and FFI observations are fixed because
`eval_def` does not inspect them. The projection is Flapjack-only: it uses the
explicit dimension adapter to interpret the arbitrary HOL word index. -/
noncomputable def CrepSemHOLFiniteState.toSourceEvaluatorState
    {ι codeEntry ffiState : Type}
    (state : CrepSemHOLFiniteState ι codeEntry ffiState) :
    CrepHolState (ι → Bool) Unit := by
  classical
  exact
    { locals := state.locals.lookup
      globals := state.globals.lookup
      code := fun _ => none
      memory := state.memory
      memaddrs := state.memaddrs
      shMemaddrs := state.shMemaddrs
      clock := state.clock
      bigEndian := state.be
      ffi := crepExpressionProjectionFfi
      baseAddress := state.baseAddr
      topAddress := state.topAddr }

end Flapjack
