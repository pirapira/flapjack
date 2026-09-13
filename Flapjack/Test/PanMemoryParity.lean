import Flapjack.PanMemory

/-!
# `panSem$mem_load` parity

The expected values in this file are the checked-in results of the direct HOL
probe in `scripts/hol-probes/pan_mem_load_probeScript.sml`.  The probe
evaluates the original `cakeml/pancake/semantics/panSemScript.sml` definition
at lines 137--166; these constants are not an independent Lean oracle.
-/

namespace Flapjack.Test.PanMemoryParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:137-166 (mem_load_def)"

def originalProbeCommand : String :=
  "scripts/hol-probes/regenerate.sh"

def originalOneHit : Option (PanValue Nat) := some (.word 3)
def originalOneMiss : Option (PanValue Nat) := none
def originalCombHit : Option (PanValue Nat) :=
  some (.rStruct [.word 3, .word 5])
def originalNamedHit : Option (PanValue Nat) :=
  some (.nStruct "Pair" [("left", .word 3), ("right", .word 5)])

def memLoadDomain : PanMemoryDomain Nat :=
  fun address => address == 10 || address == 18

def memLoadMemory : PanFlatMemory Nat :=
  fun address =>
    if address == 10 then some 3
    else if address == 18 then some 5
    else none

def memLoadContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def memLoadSuffixBlockedContext : StructContext :=
  [("Later", { fields := [], size := 1 }),
    ("Outer", { fields := [("later", .named "Later")], size := 1 })]

def valueMemLoadMemory : Nat → Option (PanValue Nat) :=
  fun address => if address == 10 then some (.word 3) else none

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:137-166 (mem_load_def)"
#guard originalProbeCommand == "scripts/hol-probes/regenerate.sh"

/- The `One` hit and miss correspond to `SOME (Val (m addr))` and `NONE`. -/
example :
    panFlatLoad [] memLoadDomain memLoadMemory 8 10 .one = originalOneHit := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatReadWord,
    panStructContextFuel, panShapeFuel, isWfShape, memLoadDomain,
    memLoadMemory, originalOneHit]

example :
    panFlatLoad [] memLoadDomain memLoadMemory 8 11 .one = originalOneMiss := by
  simp [panFlatLoad, panFlatLoadFuel, panFlatReadWord,
    panStructContextFuel, panShapeFuel, isWfShape, memLoadDomain,
    originalOneMiss]

/- The `Comb` offset is `bytes_in_word * size_of_sh_with_ctxt`, so the second
   word is at 10 + 8 * 1 = 18, exactly as in the HOL probe. -/
example :
    panFlatLoad [] memLoadDomain memLoadMemory 8 10 (.comb [.one, .one]) =
      originalCombHit := by
  simp [panFlatLoad, panFlatLoadFuel,
    panFlatLoadFuel.panFlatLoadListFuel, panFlatReadWord, panOffset,
    panStructContextFuel, panShapeFuel, panShapeFuel.panShapeListFuel,
    shapeSizeWithContext, isWfShape, isWfShape.isWfShapeList,
    memLoadDomain, memLoadMemory, originalCombHit]

/- The `Named` case reconstructs the fields with their original names. -/
example :
    panFlatLoad memLoadContext memLoadDomain memLoadMemory 8 10
      (.named "Pair") = originalNamedHit := by
  simp [panFlatLoad, panFlatLoadFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, panFlatReadWord, panOffset,
    panStructContextFuel, panShapeFieldsFuel, panShapeFuel,
    shapeSizeWithContext, isWfShape,
    lookupInfo, lookupInfoWithRest, memLoadContext, memLoadDomain,
    memLoadMemory,
    originalNamedHit]

/- The final HOL probe is deliberately not a well-formed declaration context:
   it checks the defining equation itself.  `Later` occurs before `Outer`, so
   it is outside the suffix available while loading `Outer`'s fields. -/
example :
    panFlatLoad memLoadSuffixBlockedContext memLoadDomain memLoadMemory 8 10
      (.named "Outer") = none := by
  simp [panFlatLoad, panFlatLoadFuel,
    panFlatLoadFuel.panFlatLoadFieldsFuel, panOffset, panStructContextFuel,
    panShapeFieldsFuel, panShapeFuel, shapeSizeWithContext, isWfShape,
    lookupInfo, lookupInfoWithRest, memLoadSuffixBlockedContext]

/- The structured-value loader is the source evaluator's corresponding
   boundary, so it must use the same suffix rule as `panFlatLoad`. -/
example :
    panValueFlatLoad memLoadSuffixBlockedContext valueMemLoadMemory 8 10
      (.named "Outer") = none := by
  simp [panValueFlatLoad, panValueFlatLoadFuel,
    panValueFlatLoadFieldsFuel, panValueFlatContextFuel,
    panValueFlatFieldsFuel, panValueFlatShapeFuel, isWfShape, lookupInfo,
    lookupInfoWithRest, memLoadSuffixBlockedContext]

end Flapjack.Test.PanMemoryParity
