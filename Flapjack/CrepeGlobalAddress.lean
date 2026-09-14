import Flapjack.CrepeSemantics

/-!
Type-faithful global-address boundary for `crepSem`.

CakeML's `crepSem` state stores globals in a finite map whose key type is a
*fixed* 5-bit word while the stored values have the target word width:

    globals : 5 word |-> 'a word_lab

Reference: `cakeml/pancake/semantics/crepSemScript.sml:20` (state) and
`crepSemScript.sml:111` (`eval s (LoadGlob gadr) = FLOOKUP (s.globals) gadr`).

The compact Flapjack runtime instead indexes globals by the target-width `α`,
which conflates the key and value types.  This file introduces the distinct
`CrepGlobalAddress` key type, a source-shaped lookup/store, and the state
relation that ties the source representation to the compact one.  A direct
HOL probe over the original definition is checked in at
`scripts/hol-probes/crep_eval_probeScript.sml` (fixture
`scripts/hol-probes/crep_eval_probe.out`, cases `eval_global_hit` /
`eval_global_miss`).
-/

namespace Flapjack

/-- The fixed 5-bit global-address key used by `crepSem`. -/
abbrev CrepGlobalAddress : Type := BitVec 5

/-- Re-key a target-width address into the fixed 5-bit global index space, as
the source semantics does by typing the `LoadGlob`/`StoreGlob` key at
`5 word`.  Out-of-range addresses are truncated to their low five bits. -/
def crepGlobalKey {width : Nat} (address : BitVec width) : CrepGlobalAddress :=
  BitVec.ofNat 5 address.toNat

/-- Source-shaped global state: a finite map from 5-bit keys to target words,
kept separate from ordinary memory, as in CakeML's `crepSem` state. -/
structure CrepGlobalState (α : Type u) where
  locals : Nat → Option α
  memory : α → Option α
  globals : CrepGlobalAddress → Option α := fun _ => none

/-- Source-shaped `LoadGlob`: read through the distinct 5-bit key. -/
def evalCrepGlobalLookup (globals : CrepGlobalAddress → Option α)
    (address : CrepGlobalAddress) : Option α :=
  globals address

/-- Source-shaped `StoreGlob`: update under the distinct 5-bit key.  The key
and value types differ, as in the source's `5 word |-> 'a word_lab` map. -/
def storeCrepGlobal (globals : CrepGlobalAddress → Option α)
    (address : CrepGlobalAddress) (value : α) : CrepGlobalAddress → Option α :=
  fun current => if current == address then some value else globals current

/-- The compact target-width-keyed global map and the source-faithful
5-bit-keyed map agree when the latter is exactly the former restricted along
`crepGlobalKey`.  This is the state relation that connects the port's compact
runtime representation to CakeML's typed global map. -/
def CrepGlobalAddressRelation {width : Nat} (compact : BitVec width → Option α)
    (source : CrepGlobalAddress → Option α) : Prop :=
  ∀ address, source (crepGlobalKey address) = compact address

/-- Every source-shaped global read at the re-keyed address agrees with the
compact target-width-keyed map. -/
theorem CrepGlobalAddressRelation.lookup {width : Nat}
    {compact : BitVec width → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalAddressRelation compact source) (address : BitVec width) :
    evalCrepGlobalLookup source (crepGlobalKey address) = compact address :=
  h address

/-- Hit and miss in the source-shaped representation are exactly hit and miss
in the compact one, for every in-range key. -/
theorem CrepGlobalAddressRelation.hit {width : Nat}
    {compact : BitVec width → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalAddressRelation compact source) (address : BitVec width)
    (value : α) :
    compact address = some value ↔
      evalCrepGlobalLookup source (crepGlobalKey address) = some value := by
  rw [h.lookup]

theorem CrepGlobalAddressRelation.miss {width : Nat}
    {compact : BitVec width → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalAddressRelation compact source) (address : BitVec width) :
    compact address = none ↔
      evalCrepGlobalLookup source (crepGlobalKey address) = none := by
  rw [h.lookup]

/-! Executable evaluator boundary.

    The source `LoadGlob`/`StoreGlob` clauses operate on the typed global map
    `5 word |-> 'a word_lab`.  The functions below are the executable Lean
    boundary: the key stays typed at `CrepGlobalAddress` while the values keep
    the target width `α`.  The compact runtime instead stores globals in
    `CrepState.globals : α → Option α`, keyed by the target width; the theorems
    connect the two through `CrepGlobalAddressRelation`.  Reference:
    `crepSemScript.sml:111` (LoadGlob) and `crepSemScript.sml:288-291`
    (StoreGlob); the direct HOL fixtures are checked in at
    `scripts/hol-probes/crep_eval_probeScript.sml` and
    `scripts/hol-probes/crep_store_global_probeScript.sml`. -/

/-- Executable source boundary for `LoadGlob`, the compact analogue of
`eval s (LoadGlob gadr) = FLOOKUP s.globals gadr`: the target-width address is
re-keyed to `5` bits and the typed map is read. -/
def evalCrepGlobalLoad {width : Nat} (globals : CrepGlobalAddress → Option α)
    (address : BitVec width) : Option α :=
  globals (crepGlobalKey address)

/-- Executable source boundary for `StoreGlob` at a target-width address: the
value retains the target width while the key is stored at `5` bits, as in
`set_globals dst w s`. -/
def storeCrepGlobalAt {width : Nat} (globals : CrepGlobalAddress → Option α)
    (address : BitVec width) (value : α) : CrepGlobalAddress → Option α :=
  storeCrepGlobal globals (crepGlobalKey address) value

/-- The compact global map induced by a source-faithful store.  Because the
source key space is only `5` bits, every target-width address that shares the
re-keyed key is updated. -/
def updateCrepGlobalKeyed {width : Nat} (compact : BitVec width → Option α)
    (address : BitVec width) (value : α) : BitVec width → Option α :=
  fun current =>
    if crepGlobalKey current == crepGlobalKey address then some value
    else compact current

/-- The compact `CrepState` update induced by a source-faithful global store. -/
def storeCrepStateGlobalKeyed {width : Nat} (state : CrepState (BitVec width))
    (address value : BitVec width) : CrepState (BitVec width) :=
  { state with globals := updateCrepGlobalKeyed state.globals address value }

/-- The typed `LoadGlob` boundary agrees with the compact target-width-keyed
global map under `CrepGlobalAddressRelation`. -/
theorem CrepGlobalAddressRelation.sourceLoad {width : Nat}
    {compact : BitVec width → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalAddressRelation compact source) (address : BitVec width) :
    evalCrepGlobalLoad source address = compact address :=
  h.lookup address

/-- The typed `LoadGlob` boundary reads through the compact `CrepState`. -/
theorem CrepGlobalAddressRelation.sourceLoadState {width : Nat}
    {source : CrepGlobalAddress → Option (BitVec width)}
    {state : CrepState (BitVec width)}
    (h : CrepGlobalAddressRelation state.globals source) (address : BitVec width) :
    evalCrepGlobalLoad source address = state.globals address :=
  h.sourceLoad address

/-- A source-faithful `StoreGlob` at a target-width address is observed by the
typed boundary at the same re-keyed address: the store/load round trip. -/
theorem evalCrepGlobalLoad_storeCrepGlobalAt {width : Nat}
    (globals : CrepGlobalAddress → Option α) (address : BitVec width)
    (value : α) :
    evalCrepGlobalLoad (storeCrepGlobalAt globals address value) address =
      some value := by
  simp [evalCrepGlobalLoad, storeCrepGlobalAt, storeCrepGlobal]

/-- A source-faithful `StoreGlob` leaves every unrelated `5`-bit key untouched. -/
theorem evalCrepGlobalLoad_storeCrepGlobalAt_of_ne {width : Nat}
    (globals : CrepGlobalAddress → Option α) (address : BitVec width)
    (value : α) (other : BitVec width)
    (hne : crepGlobalKey other ≠ crepGlobalKey address) :
    evalCrepGlobalLoad (storeCrepGlobalAt globals address value) other =
      evalCrepGlobalLoad globals other := by
  simp [evalCrepGlobalLoad, storeCrepGlobalAt, storeCrepGlobal, beq_iff_eq, hne]

/-- The typed store preserves `CrepGlobalAddressRelation` against the compact
map's fiber-wide update. -/
theorem CrepGlobalAddressRelation.sourceStore {width : Nat}
    {compact : BitVec width → Option α} {source : CrepGlobalAddress → Option α}
    (h : CrepGlobalAddressRelation compact source) (address : BitVec width)
    (value : α) :
    CrepGlobalAddressRelation (updateCrepGlobalKeyed compact address value)
      (storeCrepGlobalAt source address value) := by
  intro current
  simp only [updateCrepGlobalKeyed, storeCrepGlobalAt, storeCrepGlobal]
  by_cases hkey : crepGlobalKey current == crepGlobalKey address
  · simp [hkey]
  · simp [hkey, h current]

/-- The typed store preserves `CrepGlobalAddressRelation` against the compact
`CrepState`. -/
theorem CrepGlobalAddressRelation.sourceStoreState {width : Nat}
    {source : CrepGlobalAddress → Option (BitVec width)}
    {state : CrepState (BitVec width)}
    (h : CrepGlobalAddressRelation state.globals source)
    (address value : BitVec width) :
    CrepGlobalAddressRelation
      (storeCrepStateGlobalKeyed state address value).globals
      (storeCrepGlobalAt source address value) :=
  h.sourceStore address value

/-- When two distinct target-width addresses never share a re-keyed `5`-bit key,
the source-faithful compact update is exactly the compact evaluator's
`updateMemory`.  `crepGlobalKey` is injective only when the target width fits in
five bits; for wider targets this side condition records the no-aliasing case
in which the compact and source updates coincide. -/
theorem updateCrepGlobalKeyed_eq_updateMemory_of_noalias {width : Nat}
    (compact : BitVec width → Option (BitVec width))
    (address value : BitVec width)
    (hnoalias : ∀ current : BitVec width,
      crepGlobalKey current = crepGlobalKey address → current = address) :
    updateCrepGlobalKeyed compact address value = updateMemory compact address value := by
  funext current
  simp only [updateCrepGlobalKeyed, updateMemory]
  by_cases hcur : current = address
  · subst hcur
    simp
  · have hkey : crepGlobalKey current ≠ crepGlobalKey address :=
      fun hkey => hcur (hnoalias current hkey)
    simp [beq_iff_eq, hcur, hkey]

/-- No-aliasing version of `updateCrepGlobalKeyed_eq_updateMemory_of_noalias`
from injectivity of the re-keying. -/
theorem updateCrepGlobalKeyed_eq_updateMemory_of_injective {width : Nat}
    (hinj : Function.Injective (crepGlobalKey (width := width)))
    (compact : BitVec width → Option (BitVec width))
    (address value : BitVec width) :
    updateCrepGlobalKeyed compact address value = updateMemory compact address value :=
  updateCrepGlobalKeyed_eq_updateMemory_of_noalias compact address value
    (fun _ heq => hinj heq)

end Flapjack
