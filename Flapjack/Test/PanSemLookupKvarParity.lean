import Flapjack.PanSemLookupKvar

/-!
# Parity checks for `panSem$lookup_kvar_def`

The direct HOL fixture evaluates local, global, and missing-name lookups from
the original state semantics.  Lean checks cover the same three observations.
-/

namespace Flapjack.Test.PanSemLookupKvarParity

open Flapjack

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def isNone : Option (PanValue Nat) → Bool
  | none => true
  | some _ => false

def state : PanKvarState Nat :=
  { locals := fun name => if name == "x" then some (.word 5) else none
    globals := fun name => if name == "g" then some (.word 7) else none }

def localHit : Bool := isWord 5 (panSemLookupKvar state .local "x")
def globalHit : Bool := isWord 7 (panSemLookupKvar state .global "g")
def missing : Bool := isNone (panSemLookupKvar state .local "missing")

#guard localHit
#guard globalHit
#guard missing

def runChecks : IO Bool := do
  if localHit then IO.println "PASS Pan sem lookup_kvar local"
  else IO.println "FAIL Pan sem lookup_kvar local"
  if globalHit then IO.println "PASS Pan sem lookup_kvar global"
  else IO.println "FAIL Pan sem lookup_kvar global"
  if missing then IO.println "PASS Pan sem lookup_kvar missing"
  else IO.println "FAIL Pan sem lookup_kvar missing"
  pure (localHit && globalHit && missing)

end Flapjack.Test.PanSemLookupKvarParity
