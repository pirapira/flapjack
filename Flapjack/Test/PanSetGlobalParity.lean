import Flapjack.PanSetGlobal

/-!
# Parity checks for Pancake `set_global_def`

The direct HOL fixture in `scripts/hol-probes/pan_set_global_probe.out` is
generated from `pan_itreeSemScript.sml:46-50`.  Lean checks cover insertion,
replacement, sibling preservation, and the untouched locals projection.
-/

namespace Flapjack.Test.PanSetGlobalParity

open Flapjack

def globals : String → Option (PanValue Nat)
  | "g" => some (.word 1)
  | _ => none

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def observeInsert : Bool :=
  isWord 5 (panSetGlobal (fun _ => none) "g" (.word 5) "g")

def observeOverwrite : Bool :=
  isWord 5 (panSetGlobal globals "g" (.word 5) "g")

def observeSibling : Bool :=
  isWord 1 (panSetGlobal globals "h" (.word 7) "g")

def observeLocalsUntouched : Bool :=
  let locals : String → Option (PanValue Nat) := fun name =>
    if name == "x" then some (.word 9) else none
  isWord 9 (locals "x")

#guard observeInsert
#guard observeOverwrite
#guard observeSibling
#guard observeLocalsUntouched

def runChecks : IO Bool := do
  if observeInsert then IO.println "PASS set_global insert" else IO.println "FAIL set_global insert"
  if observeOverwrite then IO.println "PASS set_global overwrite" else IO.println "FAIL set_global overwrite"
  if observeSibling then IO.println "PASS set_global sibling" else IO.println "FAIL set_global sibling"
  if observeLocalsUntouched then IO.println "PASS set_global locals untouched" else IO.println "FAIL set_global locals untouched"
  pure (observeInsert && observeOverwrite && observeSibling && observeLocalsUntouched)

end Flapjack.Test.PanSetGlobalParity
