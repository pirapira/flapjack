import Flapjack.PanSetKvar

/-!
# Parity checks for Pancake `set_kvar_def`

The direct HOL fixture in `scripts/hol-probes/pan_set_kvar_probe.out` is
generated from `pan_itreeSemScript.sml:53-58`.  Lean checks cover local and
global insertion plus preservation of the opposite environment.
-/

namespace Flapjack.Test.PanSetKvarParity

open Flapjack

def initial : PanKvarState Nat where
  locals := fun name => if name == "x" then some (.word 1) else none
  globals := fun name => if name == "g" then some (.word 2) else none

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def observeLocal : Bool :=
  isWord 5 ((panSetKvar initial .local "x" (.word 5)).locals "x")

def observeGlobal : Bool :=
  isWord 7 ((panSetKvar initial .global "g" (.word 7)).globals "g")

def observeLocalKeepsGlobal : Bool :=
  isWord 2 ((panSetKvar initial .local "y" (.word 5)).globals "g")

def observeGlobalKeepsLocal : Bool :=
  isWord 1 ((panSetKvar initial .global "h" (.word 7)).locals "x")

#guard observeLocal
#guard observeGlobal
#guard observeLocalKeepsGlobal
#guard observeGlobalKeepsLocal

def runChecks : IO Bool := do
  if observeLocal then IO.println "PASS set_kvar local" else IO.println "FAIL set_kvar local"
  if observeGlobal then IO.println "PASS set_kvar global" else IO.println "FAIL set_kvar global"
  if observeLocalKeepsGlobal then IO.println "PASS set_kvar local preserves globals" else IO.println "FAIL set_kvar local preserves globals"
  if observeGlobalKeepsLocal then IO.println "PASS set_kvar global preserves locals" else IO.println "FAIL set_kvar global preserves locals"
  pure (observeLocal && observeGlobal && observeLocalKeepsGlobal && observeGlobalKeepsLocal)

end Flapjack.Test.PanSetKvarParity
