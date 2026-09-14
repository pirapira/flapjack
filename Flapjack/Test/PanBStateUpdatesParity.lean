import Flapjack.PanBStateUpdates

/-!
# Parity checks for Pancake `set_var_def` on `bstate`

The direct HOL fixture in `scripts/hol-probes/pan_itree_set_var_probe.out`
evaluates `pan_itreeSem`'s `set_var_def`.  This test exercises insertion,
overwrite, sibling preservation, and preservation of globals/memory.
-/

namespace Flapjack.Test.PanBStateUpdatesParity

open Flapjack

def baseState : PanBState Nat where
  locals := updatePanValueMap (updatePanValueMap (fun _ => none)
    "x" (.word 5)) "y" (.word 7)
  globals := updatePanValueMap (fun _ => none) "g" (.word 1)
  structs := []
  code := fun _ => none
  exceptionShapes := fun _ => none
  memory := fun address => if address == 9 then some (.word 13) else none
  memaddrs := fun address => address == 9
  sharedMemaddrs := fun _ => false
  be := false
  baseAddress := 100
  topAddress := 200

def isWord (values : VarName → Option (PanValue Nat))
    (name : VarName) (expected : Nat) : Bool :=
  match values name with
  | some (.word value) => value == expected
  | _ => false

def observeNew : Bool :=
  isWord (panBSetVar baseState "z" (.word 9)).locals "z" 9

def observeOverwrite : Bool :=
  isWord (panBSetVar baseState "x" (.word 9)).locals "x" 9

def observeSibling : Bool :=
  isWord (panBSetVar baseState "x" (.word 9)).locals "y" 7

def observeOtherFields : Bool :=
  isWord (panBSetVar baseState "x" (.word 9)).globals "g" 1 &&
    ((panBSetVar baseState "x" (.word 9)).memory 9).isSome &&
    (panBSetVar baseState "x" (.word 9)).baseAddress == 100 &&
    (panBSetVar baseState "x" (.word 9)).topAddress == 200

#guard observeNew
#guard observeOverwrite
#guard observeSibling
#guard observeOtherFields

def runChecks : IO Bool := do
  if observeNew then IO.println "PASS bstate set_var inserts local"
  else IO.println "FAIL bstate set_var inserts local"
  if observeOverwrite then IO.println "PASS bstate set_var overwrites local"
  else IO.println "FAIL bstate set_var overwrites local"
  if observeSibling then IO.println "PASS bstate set_var preserves sibling"
  else IO.println "FAIL bstate set_var preserves sibling"
  if observeOtherFields then IO.println "PASS bstate set_var preserves other fields"
  else IO.println "FAIL bstate set_var preserves other fields"
  pure (observeNew && observeOverwrite && observeSibling && observeOtherFields)

end Flapjack.Test.PanBStateUpdatesParity
