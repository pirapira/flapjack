import Flapjack.PanLookupKvar

/-!
# Parity checks for Pancake `lookup_kvar_def`

The direct HOL fixture in `scripts/hol-probes/pan_lookup_kvar_probe.out` is
generated from `pan_itreeSemScript.sml:60-64`.  Lean checks cover local and
global hits and missing bindings.
-/

namespace Flapjack.Test.PanLookupKvarParity

open Flapjack

def state : PanKvarState Nat where
  locals := fun name => if name == "x" then some (.word 1) else none
  globals := fun name => if name == "g" then some (.word 2) else none

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def observeLocal : Bool := isWord 1 (panLookupKvar state .local "x")
def observeGlobal : Bool := isWord 2 (panLookupKvar state .global "g")
def observeMissing : Bool := (panLookupKvar state .local "missing").isNone

#guard observeLocal
#guard observeGlobal
#guard observeMissing

def runChecks : IO Bool := do
  if observeLocal then IO.println "PASS lookup_kvar local" else IO.println "FAIL lookup_kvar local"
  if observeGlobal then IO.println "PASS lookup_kvar global" else IO.println "FAIL lookup_kvar global"
  if observeMissing then IO.println "PASS lookup_kvar missing" else IO.println "FAIL lookup_kvar missing"
  pure (observeLocal && observeGlobal && observeMissing)

end Flapjack.Test.PanLookupKvarParity
