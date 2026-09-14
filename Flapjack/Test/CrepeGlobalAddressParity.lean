import Flapjack.CrepeGlobalAddress

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
          compactGlobals (BitVec.ofNat 64 4)) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  return results.all id

end Flapjack.Test.CrepeGlobalAddressParity
