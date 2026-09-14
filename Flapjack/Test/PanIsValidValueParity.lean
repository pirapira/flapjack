import Flapjack.PanIsValidValue

/-!
# Parity checks for Pancake `is_valid_value_def`

The direct HOL fixture in `scripts/hol-probes/pan_is_valid_value_probe.out` is
generated from `pan_itreeSemScript.sml:67-74`.  Lean checks cover matching
local/global shapes, missing bindings, and a shape mismatch.
-/

namespace Flapjack.Test.PanIsValidValueParity

open Flapjack

def structs : StructContext := []

def state : PanKvarState Nat where
  locals := fun name => if name == "x" then some (.word 1) else none
  globals := fun name => if name == "g" then some (.rStruct [.word 2, .word 3]) else none

def observeLocal : Bool :=
  panIsValidValue structs state .local "x" (.word 9)

def observeGlobal : Bool :=
  panIsValidValue structs state .global "g" (.rStruct [.word 4, .word 5])

def observeMissing : Bool :=
  !(panIsValidValue structs state .local "missing" (.word 9))

def observeMismatch : Bool :=
  !(panIsValidValue structs state .global "g" (.word 9))

#guard observeLocal
#guard observeGlobal
#guard observeMissing
#guard observeMismatch

def runChecks : IO Bool := do
  if observeLocal then IO.println "PASS is_valid_value local shape" else IO.println "FAIL is_valid_value local shape"
  if observeGlobal then IO.println "PASS is_valid_value global shape" else IO.println "FAIL is_valid_value global shape"
  if observeMissing then IO.println "PASS is_valid_value missing" else IO.println "FAIL is_valid_value missing"
  if observeMismatch then IO.println "PASS is_valid_value mismatch" else IO.println "FAIL is_valid_value mismatch"
  pure (observeLocal && observeGlobal && observeMissing && observeMismatch)

end Flapjack.Test.PanIsValidValueParity
