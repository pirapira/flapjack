import Flapjack.CrepeGlobalEvaluator

/-!
Parity test for the source-faithful Crep global-address boundary.

Expected values are transcribed from the direct HOL-EVAL probe of the original
definition in `cakeml/pancake/semantics/crepSemScript.sml:111`
(`LoadGlob gadr = FLOOKUP s.globals gadr`), checked in as
`scripts/hol-probes/crep_eval_probe.out`:
    eval_global_hit=SOME (Word 11w)
    eval_global_miss=NONE
Here the probe state was an 8-bit target word with globals keyed at `5 word`
(the probe uses `crepLang$LoadGlob (4w:5 word)` for the hit and
`crepLang$LoadGlob (8w:5 word)` for the miss).
-/

namespace Flapjack.Test.CrepeGlobalAddressParity

open Flapjack

/-- Active globals: key `4` maps to value `11`, mirroring the HOL probe. -/
def probeGlobals : CrepGlobalAddress → Option (BitVec 8) :=
  fun address => if address == BitVec.ofNat 5 4 then some (BitVec.ofNat 8 11) else none

def probeState : CrepGlobalState (BitVec 8) :=
  { locals := fun _ => none
    memory := fun _ => none
    globals := probeGlobals }

def readNat : Option (BitVec 8) → Option Nat
  | none => none
  | some value => some value.toNat

def hitValue : Option Nat :=
  readNat (evalCrepGlobalLookup probeState.globals (BitVec.ofNat 5 4))

def missValue : Option Nat :=
  readNat (evalCrepGlobalLookup probeState.globals (BitVec.ofNat 5 8))

/-- A compact 64-bit-target map consistent under 5-bit re-keying, and the
source-shaped map related to it. -/
def compactGlobals : BitVec 64 → Option Nat :=
  fun address => if crepGlobalKey address == BitVec.ofNat 5 4 then some 11 else none

def sourceGlobals : CrepGlobalAddress → Option Nat :=
  fun address => if address == BitVec.ofNat 5 4 then some 11 else none

example : hitValue = some 11 := by decide
example : missValue = none := by decide

example : crepGlobalKey (BitVec.ofNat 64 4) = BitVec.ofNat 5 4 := by decide
example : crepGlobalKey (BitVec.ofNat 64 36) = BitVec.ofNat 5 4 := by decide
example : crepGlobalKey (BitVec.ofNat 8 8) = BitVec.ofNat 5 8 := by decide

/-- The re-keyed source-shaped lookup always agrees with the compact map. -/
example : CrepGlobalAddressRelation compactGlobals sourceGlobals := by
  intro address
  simp [compactGlobals, sourceGlobals]

/-! Typed store parity, transcribed from the direct HOL-EVAL probe of
`crepSemScript.sml:288-291` (`StoreGlob`), checked in as
`scripts/hol-probes/crep_store_global_probe.out`:
    store_global_insert=(NONE,SOME (Word 11w))
    store_global_update_sibling=(NONE,SOME (Word 22w),SOME (Word 9w))
    store_global_eval_failure=(SOME Error,SOME (Word 11w))
The probe stores at `crepLang$StoreGlob (4w:5 word)` with 8-bit values; the
functions below re-key target-width addresses to the same `5`-bit key.  The
eval-failure case is a source-expression evaluation error, so it correctly
leaves the typed boundary unchanged (checked via `failureValue`). -/

/-- Active globals for the store probe: key `4` maps to `11`, sibling key `8`
maps to `9`. -/
def storeSourceGlobals : CrepGlobalAddress → Option (BitVec 8) :=
  fun address =>
    if address == BitVec.ofNat 5 4 then some (BitVec.ofNat 8 11)
    else if address == BitVec.ofNat 5 8 then some (BitVec.ofNat 8 9)
    else none

def insertGlobals : CrepGlobalAddress → Option (BitVec 8) :=
  storeCrepGlobalAt (fun _ => none) (BitVec.ofNat 64 4) (BitVec.ofNat 8 11)

def updatedGlobals : CrepGlobalAddress → Option (BitVec 8) :=
  storeCrepGlobalAt storeSourceGlobals (BitVec.ofNat 64 4) (BitVec.ofNat 8 22)

def insertValue : Option Nat :=
  readNat (evalCrepGlobalLoad insertGlobals (BitVec.ofNat 64 4))

def updatedValue : Option Nat :=
  readNat (evalCrepGlobalLoad updatedGlobals (BitVec.ofNat 64 4))

def siblingValue : Option Nat :=
  readNat (evalCrepGlobalLoad updatedGlobals (BitVec.ofNat 64 8))

def failureValue : Option Nat :=
  readNat (evalCrepGlobalLoad storeSourceGlobals (BitVec.ofNat 64 4))

example : insertValue = some 11 := by decide
example : updatedValue = some 22 := by decide
example : siblingValue = some 9 := by decide
example : failureValue = some 11 := by decide

/-- The boundary store/load round trip, matching `store_global_insert`. -/
example :
    evalCrepGlobalLoad insertGlobals (BitVec.ofNat 64 4) = some (BitVec.ofNat 8 11) :=
  evalCrepGlobalLoad_storeCrepGlobalAt (fun _ => none) (BitVec.ofNat 64 4) (BitVec.ofNat 8 11)

/-- The typed store preserves the compact-state relation, as required to thread
the boundary through `CrepState`. -/
example :
    CrepGlobalAddressRelation
      (updateCrepGlobalKeyed compactGlobals (BitVec.ofNat 64 4) 22)
      (storeCrepGlobalAt sourceGlobals (BitVec.ofNat 64 4) 22) :=
  (show CrepGlobalAddressRelation compactGlobals sourceGlobals from by
    intro address
    simp [compactGlobals, sourceGlobals]).sourceStore (BitVec.ofNat 64 4) 22

/-! Executable evaluator-entrypoint parity for the typed global-key model.

The typed evaluator reads `LoadGlob` through the fixed 5-bit key and its
`StoreGlob` entrypoint writes under that key, so target-width addresses that
share a re-keyed key observe the same value, exactly as the source
`5 word |-> 'a word_lab` map.  The `Nat` fixture word model is the same one
used by `evalCrepFullExpState`, so these checks run the executable
entrypoints directly. -/

/-- The `Nat` fixture re-keying into the source's fixed 5-bit index space. -/
def typedKey : Nat → CrepGlobalAddress := crepGlobalKeyOfNat

def typedBaseState : CrepGlobalState Nat :=
  { locals := fun _ => none
    memory := fun _ => none
    globals := fun _ => none }

def typedStored : CrepGlobalState Nat :=
  storeCrepTypedGlobal typedKey typedBaseState 4 11

def typedSiblingState : CrepGlobalState Nat :=
  { typedBaseState with globals := fun address => if address = 8 then some 9 else none }

def typedSiblingStored : CrepGlobalState Nat :=
  storeCrepTypedGlobal typedKey typedSiblingState 4 11

def typedInsertValue : Option Nat := evalCrepTypedLoad typedKey typedStored 4
def typedAliasValue : Option Nat := evalCrepTypedLoad typedKey typedStored 36
def typedSiblingValue : Option Nat := evalCrepTypedLoad typedKey typedSiblingStored 8
def typedExpValue : Option Nat :=
  evalCrepTypedExp typedKey typedStored 0 100 (.loadGlob 4)

example : typedInsertValue = some 11 := by decide
example : typedAliasValue = some 11 := by decide
example : typedSiblingValue = some 9 := by decide
example : typedExpValue = some 11 := by
  simp [typedExpValue, evalCrepTypedExp, typedStored,
    storeCrepTypedGlobal, storeCrepGlobal, typedKey, crepGlobalKeyOfNat]

/-- The typed store/load round trip through the executable entrypoint. -/
example : evalCrepTypedLoad typedKey typedStored 4 = some 11 :=
  evalCrepTypedLoad_storeCrepTypedGlobal typedKey typedBaseState 4 11

/-- The evaluator `loadGlob` case is the typed load entrypoint. -/
example : evalCrepTypedExp typedKey typedStored 0 100 (.loadGlob 4) =
    evalCrepTypedLoad typedKey typedStored 4 :=
  evalCrepTypedExp_loadGlob typedKey typedStored 0 100 4

/-- Projecting the typed state onto the compact state relates the two maps. -/
example : CrepGlobalKeyRelation typedKey (typedStored.toCompact typedKey).globals
    typedStored.globals :=
  CrepGlobalState.relation_toCompact typedKey typedStored

/-- On a fixed 5-bit address space `id` never aliases, so the fiber-wide typed
update is exactly the compact evaluator's `updateMemory`, the connection used
by `evalCrepFullProgState`'s `StoreGlob` clause. -/
example (compact : BitVec 5 → Option (BitVec 5)) (address value : BitVec 5) :
    updateCrepGlobalKeyedBy id compact address value =
      updateMemory compact address value :=
  updateCrepGlobalKeyedBy_eq_updateMemory_of_noalias id compact address value
    (fun _ h => h)

/-- Projecting the typed store entrypoint onto the compact state is exactly the
compact `StoreGlob` state update under no aliasing. -/
example (state : CrepGlobalState (BitVec 5)) (address value : BitVec 5) :
    (storeCrepTypedGlobal id state address value).toCompact id =
      { (state.toCompact id) with
        globals := updateMemory (state.toCompact id).globals address value } :=
  CrepGlobalState.toCompact_store_of_noalias id state address value (fun _ h => h)

def runChecks : IO Bool := do
  let checks :=
    [ ("Crep global LoadGlob hits the source 5-bit key", hitValue == some 11),
      ("Crep global LoadGlob misses an absent 5-bit key", missValue == none),
      ("Crep global key re-types a 64-bit address to 5 bits",
        crepGlobalKey (BitVec.ofNat 64 4) == BitVec.ofNat 5 4),
      ("Crep global key truncates an out-of-range address",
        crepGlobalKey (BitVec.ofNat 64 36) == BitVec.ofNat 5 4),
      ("Crep global state relation restricts the compact map to 5-bit keys",
        sourceGlobals (crepGlobalKey (BitVec.ofNat 64 4)) ==
          compactGlobals (BitVec.ofNat 64 4)),
      ("Crep typed StoreGlob inserts at the 5-bit key", insertValue == some 11),
      ("Crep typed StoreGlob updates the 5-bit key", updatedValue == some 22),
      ("Crep typed StoreGlob leaves a sibling 5-bit key untouched",
        siblingValue == some 9),
      ("Crep typed StoreGlob without a value leaves globals unchanged",
        failureValue == some 11),
      ("Crep typed evaluator StoreGlob entrypoint inserts at the 5-bit key",
        typedInsertValue == some 11),
      ("Crep typed evaluator aliases 36 and 4 to the same 5-bit key",
        typedAliasValue == some 11),
      ("Crep typed evaluator leaves a sibling 5-bit key untouched",
        typedSiblingValue == some 9),
      ("Crep typed evaluator LoadGlob entrypoint reads the typed key",
        typedExpValue == some 11) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  return results.all id

end Flapjack.Test.CrepeGlobalAddressParity
