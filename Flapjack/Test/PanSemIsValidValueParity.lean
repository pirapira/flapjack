import Flapjack.PanSemIsValidValue

/-!
# Parity checks for `panSem$is_valid_value_def`

The direct HOL fixture covers local/global shape hits, shape mismatch, and a
missing binding.  Lean checks cover the same source cases.
-/

namespace Flapjack.Test.PanSemIsValidValueParity

open Flapjack

def state : PanKvarState Nat :=
  { locals := fun name => if name == "x" then some (.word 5) else none
    globals := fun name => if name == "g" then some (.word 7) else none }

def localShape : Bool :=
  panSemIsValidValue [] state .local "x" (.word 9)

def globalShape : Bool :=
  panSemIsValidValue [] state .global "g" (.word 9)

def mismatch : Bool :=
  !panSemIsValidValue [] state .local "x" (.rStruct [])

def missing : Bool :=
  !panSemIsValidValue [] state .local "missing" (.word 9)

#guard localShape
#guard globalShape
#guard mismatch
#guard missing

def runChecks : IO Bool := do
  if localShape then IO.println "PASS Pan sem is_valid_value local shape"
  else IO.println "FAIL Pan sem is_valid_value local shape"
  if globalShape then IO.println "PASS Pan sem is_valid_value global shape"
  else IO.println "FAIL Pan sem is_valid_value global shape"
  if mismatch then IO.println "PASS Pan sem is_valid_value mismatch"
  else IO.println "FAIL Pan sem is_valid_value mismatch"
  if missing then IO.println "PASS Pan sem is_valid_value missing"
  else IO.println "FAIL Pan sem is_valid_value missing"
  pure (localShape && globalShape && mismatch && missing)

end Flapjack.Test.PanSemIsValidValueParity
