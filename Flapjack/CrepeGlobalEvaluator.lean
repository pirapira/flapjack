import Flapjack.CrepeGlobalAddress

/-!
Executable evaluator entrypoint for the typed Crep global-key model.

`CrepeGlobalAddress` gives the source-faithful 5-bit global map and its
single-key `LoadGlob`/`StoreGlob` boundary.  This module threads that typed
model into an executable Crep state and evaluator entrypoint:

* `CrepGlobalState.toCompact` projects a typed-globals state onto the compact
  target-width-keyed `CrepState`, re-keying every global read along the source
  key function;
* `evalCrepTypedExp` is the executable expression entrypoint (`eval`) that
  reads globals through the typed key;
* `storeCrepTypedGlobal` is the executable `evaluate` entrypoint for
  `StoreGlob`, writing under the typed key while values retain the target
  width.

The connection theorems show that projecting the typed store back to the
compact state is exactly the compact evaluator's `updateMemory` global update
under the no-aliasing side condition, so no target-width-keyed source
semantics is reintroduced.

Reference: `cakeml/pancake/semantics/crepSemScript.sml:20` (state), `:61-63`
(`set_globals`), `:111` (`eval (LoadGlob gadr)`), `:288-291`
(`evaluate (StoreGlob dst src, s)`).
-/

namespace Flapjack

/-- Re-key a `Nat`-valued fixture address into the source's fixed 5-bit global
index.  The fixture word model uses `Nat` values, so this is the `Nat`
instance of `crepGlobalKey`. -/
def crepGlobalKeyOfNat (address : Nat) : CrepGlobalAddress :=
  BitVec.ofNat 5 address

/-- Generic state relation between a target-width-keyed compact map and a typed
5-bit-keyed source map, parameterized by the re-keying function.  This
generalizes `CrepGlobalAddressRelation` beyond `BitVec width` so the same
relation can compare the `Nat` fixture evaluator against the typed
representation. -/
def CrepGlobalKeyRelation {α : Type u} (key : α → CrepGlobalAddress)
    (compact : α → Option α) (source : CrepGlobalAddress → Option α) : Prop :=
  ∀ address, source (key address) = compact address

/-- The compact global map induced by a typed store: every address sharing the
re-keyed key is updated. -/
def updateCrepGlobalKeyedBy {α : Type u} [BEq α] (key : α → CrepGlobalAddress)
    (compact : α → Option α) (address value : α) : α → Option α :=
  fun current => if key current == key address then some value else compact current

/-- Project a typed-globals Crep state onto the compact target-width-keyed
`CrepState`, re-keying every global read along `key`.  This is the state
entrypoint that threads the typed model into the compact evaluator. -/
def CrepGlobalState.toCompact {α : Type u} (key : α → CrepGlobalAddress)
    (state : CrepGlobalState α) : CrepState α :=
  { locals := state.locals
    memory := state.memory
    globals := fun address => state.globals (key address) }

/-- The typed state relates to the compact state obtained by projecting it. -/
theorem CrepGlobalState.relation_toCompact {α : Type u}
    (key : α → CrepGlobalAddress) (state : CrepGlobalState α) :
    CrepGlobalKeyRelation key (state.toCompact key).globals state.globals :=
  fun _ => rfl

/-- Executable source-faithful expression entrypoint (`eval`) on the typed
state.  Every case matches the compact `evalCrepFullExpState`, except
`loadGlob`, which reads through the fixed 5-bit key as the source
`eval s (LoadGlob gadr) = FLOOKUP s.globals gadr` does. -/
def evalCrepTypedExp {α : Type u} [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α] [DecidableRel (fun left right : α => left < right)]
    [PanCmp α] (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (baseAddress topAddress : α) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address | .load32 address | .loadByte address => do
      let address ← evalCrepTypedExp key state baseAddress topAddress address
      state.memory address
  | .loadGlob address => state.globals (key address)
  | .op operator [left, right] => do
      let left ← evalCrepTypedExp key state baseAddress topAddress left
      let right ← evalCrepTypedExp key state baseAddress topAddress right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepTypedExp key state baseAddress topAddress left
      let right ← evalCrepTypedExp key state baseAddress topAddress right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepTypedExp key state baseAddress topAddress left
      let right ← evalCrepTypedExp key state baseAddress topAddress right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepTypedExp key state baseAddress topAddress left
      let right ← evalCrepTypedExp key state baseAddress topAddress right
      evalPanShift operator left right
  | .baseAddr => some baseAddress
  | .topAddr => some topAddress
  | _ => none
termination_by expression => sizeOf expression

/-- Executable `LoadGlob` entrypoint on the typed state: read the 5-bit key. -/
def evalCrepTypedLoad {α : Type u} (key : α → CrepGlobalAddress)
    (state : CrepGlobalState α) (address : α) : Option α :=
  state.globals (key address)

/-- Executable `StoreGlob` entrypoint on the typed state: update under the
5-bit key while the value keeps the target width `α`. -/
def storeCrepTypedGlobal {α : Type u} [BEq α] (key : α → CrepGlobalAddress)
    (state : CrepGlobalState α) (address value : α) : CrepGlobalState α :=
  { state with globals := storeCrepGlobal state.globals (key address) value }

/-- The evaluator's `loadGlob` case is exactly the typed load entrypoint. -/
theorem evalCrepTypedExp_loadGlob {α : Type u} [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α]
    [ShiftRight α] [LT α] [DecidableRel (fun left right : α => left < right)]
    [PanCmp α] (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (baseAddress topAddress : α) (address : α) :
    evalCrepTypedExp key state baseAddress topAddress (.loadGlob address) =
      evalCrepTypedLoad key state address := by
  simp [evalCrepTypedExp, evalCrepTypedLoad]

/-- A typed store followed by a typed load at the same address returns the
stored value, the executable source `StoreGlob`/`LoadGlob` round trip. -/
theorem evalCrepTypedLoad_storeCrepTypedGlobal {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (address value : α) :
    evalCrepTypedLoad key (storeCrepTypedGlobal key state address value) address =
      some value := by
  simp [evalCrepTypedLoad, storeCrepTypedGlobal, storeCrepGlobal]

/-- A typed store leaves every address with a different 5-bit key untouched. -/
theorem evalCrepTypedLoad_storeCrepTypedGlobal_of_ne {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (address value : α) (other : α) (hne : key other ≠ key address) :
    evalCrepTypedLoad key (storeCrepTypedGlobal key state address value) other =
      evalCrepTypedLoad key state other := by
  simp [evalCrepTypedLoad, storeCrepTypedGlobal, storeCrepGlobal, beq_iff_eq, hne]

/-- The typed store preserves the state relation against the compact fiber-wide
update. -/
theorem CrepGlobalKeyRelation.store {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress)
    {compact : α → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalKeyRelation key compact source) (address value : α) :
    CrepGlobalKeyRelation key
      (updateCrepGlobalKeyedBy key compact address value)
      (storeCrepGlobal source (key address) value) := by
  intro current
  simp only [updateCrepGlobalKeyedBy, storeCrepGlobal]
  by_cases hkey : key current == key address
  · simp [hkey]
  · simp [hkey, h current]

/-- Projecting the typed store back to the compact state is exactly the
fiber-wide update of the projected compact global map. -/
theorem CrepGlobalState.toCompact_store {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (address value : α) :
    (storeCrepTypedGlobal key state address value).toCompact key =
      { (state.toCompact key) with
        globals := updateCrepGlobalKeyedBy key (state.toCompact key).globals
          address value } := by
  have h : (fun current => (storeCrepGlobal state.globals (key address) value)
        (key current)) =
      updateCrepGlobalKeyedBy key (state.toCompact key).globals address value := by
    funext current
    simp [CrepGlobalState.toCompact, updateCrepGlobalKeyedBy, storeCrepGlobal,
      beq_iff_eq]
  simp [CrepGlobalState.toCompact, storeCrepTypedGlobal, h]

/-- When distinct addresses never share a re-keyed 5-bit key, the fiber-wide
typed update is exactly the compact evaluator's `updateMemory`. -/
theorem updateCrepGlobalKeyedBy_eq_updateMemory_of_noalias {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (compact : α → Option α) (address value : α)
    (hnoalias : ∀ current, key current = key address → current = address) :
    updateCrepGlobalKeyedBy key compact address value =
      updateMemory compact address value := by
  funext current
  simp only [updateCrepGlobalKeyedBy, updateMemory, beq_iff_eq]
  by_cases hcur : current = address
  · subst hcur
    simp
  · have hkey : key current ≠ key address :=
      fun hkey => hcur (hnoalias current hkey)
    simp [hcur, hkey]

/-- Under the no-aliasing side condition, projecting the typed store back to
the compact state is exactly the compact evaluator's `StoreGlob` state update
(`updateMemory`). -/
theorem CrepGlobalState.toCompact_store_of_noalias {α : Type u} [BEq α] [LawfulBEq α]
    (key : α → CrepGlobalAddress) (state : CrepGlobalState α)
    (address value : α)
    (hnoalias : ∀ current, key current = key address → current = address) :
    (storeCrepTypedGlobal key state address value).toCompact key =
      { (state.toCompact key) with
        globals := updateMemory (state.toCompact key).globals address value } := by
  rw [CrepGlobalState.toCompact_store,
    updateCrepGlobalKeyedBy_eq_updateMemory_of_noalias key _ address value hnoalias]

/-- Executable entrypoint agreement: running the compact evaluator's
`StoreGlob` then `LoadGlob` on the projected typed state returns the same
value, and its resulting global map is the projection of the typed store
entrypoint, under the no-aliasing side condition.  This threads the typed
model into the compact evaluator's program boundary. -/
theorem evalCrepFullProgState_storeGlob_loadGlob_toCompact_of_noalias
    {α : Type u} [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (key : α → CrepGlobalAddress)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepGlobalState α)
    (address value : α)
    (hnoalias : ∀ current, key current = key address → current = address) :
    evalCrepFullProgState [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) (state.toCompact key)
      (.seq (.storeGlob address (.const value))
        (.return [.loadGlob address])) =
      some (.returned
        ((storeCrepTypedGlobal key state address value).toCompact key) [value]) := by
  rw [evalCrepFullProgState_storeGlob_loadGlob]
  rw [← CrepGlobalState.toCompact_store_of_noalias key state address value hnoalias]

end Flapjack
