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

end Flapjack
