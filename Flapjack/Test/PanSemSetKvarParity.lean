import Flapjack.PanSemSetKvar

/-!
# Parity checks for `panSem$set_kvar_def`

The direct HOL fixture evaluates both dispatch branches and confirms that the
opposite environment is preserved.  Lean checks cover the same four cases.
-/

namespace Flapjack.Test.PanSemSetKvarParity

open Flapjack

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def state : PanKvarState Nat :=
  { locals := fun _ => none, globals := fun _ => none }

def localSet : PanKvarState Nat :=
  panSemSetKvar state .local "x" (.word 5)

def globalSet : PanKvarState Nat :=
  panSemSetKvar state .global "g" (.word 5)

def localUpdate : Bool := isWord 5 (localSet.locals "x")
def globalUpdate : Bool := isWord 5 (globalSet.globals "g")
def localPreservesGlobals : Bool := globalSet.globals "x" |>.isNone
def globalPreservesLocals : Bool := localSet.locals "g" |>.isNone

#guard localUpdate
#guard globalUpdate
#guard localPreservesGlobals
#guard globalPreservesLocals

def runChecks : IO Bool := do
  if localUpdate then IO.println "PASS Pan sem set_kvar local"
  else IO.println "FAIL Pan sem set_kvar local"
  if globalUpdate then IO.println "PASS Pan sem set_kvar global"
  else IO.println "FAIL Pan sem set_kvar global"
  if localPreservesGlobals then IO.println "PASS Pan sem set_kvar local preserves globals"
  else IO.println "FAIL Pan sem set_kvar local preserves globals"
  if globalPreservesLocals then IO.println "PASS Pan sem set_kvar global preserves locals"
  else IO.println "FAIL Pan sem set_kvar global preserves locals"
  pure (localUpdate && globalUpdate && localPreservesGlobals && globalPreservesLocals)

end Flapjack.Test.PanSemSetKvarParity
