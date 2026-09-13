import Flapjack.PanMemory

/-!
# Pancake word-store parity

The expected results are from the direct HOL probe in
`scripts/hol-probes/pan_flat_store_probe.out`, evaluating
`mem_store_def` and `mem_stores_def` in
`cakeml/pancake/semantics/panSemScript.sml:373-386`.
-/

namespace Flapjack.Test.PanFlatStoreParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:373-386 (mem_store_def/mem_stores_def)"

def domain : PanMemoryDomain Nat :=
  fun address => address == 10 || address == 18

def memory : PanFlatMemory Nat := fun _ => some 0

def originalStoreHit : Option Nat := some 3
def originalStoreMiss : Option Nat := none
def originalStoresHit : Option (Nat × Nat) := some (3, 5)
def originalStoresBlocked : Option (Nat × Nat) := none

def storeHit : Option Nat := do
  let updated ← panFlatStoreWord domain memory 10 3
  updated 10

def storeMiss : Option Nat := do
  let updated ← panFlatStoreWord domain memory 11 3
  updated 11

def storesHit : Option (Nat × Nat) := do
  let updated ← panFlatStoreWords domain memory 8 10 [3, 5]
  let left ← updated 10
  let right ← updated 18
  pure (left, right)

def storesBlocked : Option (Nat × Nat) := do
  let updated ← panFlatStoreWords (fun address => address == 10) memory 8 10 [3, 5]
  let left ← updated 10
  let right ← updated 18
  pure (left, right)

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:373-386 (mem_store_def/mem_stores_def)"
#guard storeHit == originalStoreHit
#guard storeMiss == originalStoreMiss
#guard storesHit == originalStoresHit
#guard storesBlocked == originalStoresBlocked

end Flapjack.Test.PanFlatStoreParity
