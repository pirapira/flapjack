import Flapjack.PanBStateEmptyLocals

/-!
# Parity checks for interaction-tree `empty_locals_def`

The direct HOL fixture in `scripts/hol-probes/pan_itree_empty_locals_probe.out`
evaluates the original `bstate` record update.  The checks cover clearing
locals and preserving representative sibling state.
-/

namespace Flapjack.Test.PanBStateEmptyLocalsParity

open Flapjack

def baseState : PanBState Nat where
  locals := updatePanValueMap (fun _ => none) "x" (.word 5)
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

def observeLocalsCleared : Bool :=
  ((panBEmptyLocals baseState).locals "x").isNone &&
    ((panBEmptyLocals baseState).locals "other").isNone

def observeSiblingsPreserved : Bool :=
  isWord (panBEmptyLocals baseState).globals "g" 1 &&
    ((panBEmptyLocals baseState).memory 9).isSome &&
    (panBEmptyLocals baseState).baseAddress == 100 &&
    (panBEmptyLocals baseState).topAddress == 200

#guard observeLocalsCleared
#guard observeSiblingsPreserved

def runChecks : IO Bool := do
  if observeLocalsCleared then
    IO.println "PASS bstate empty_locals clears locals"
  else
    IO.println "FAIL bstate empty_locals clears locals"
  if observeSiblingsPreserved then
    IO.println "PASS bstate empty_locals preserves siblings"
  else
    IO.println "FAIL bstate empty_locals preserves siblings"
  pure (observeLocalsCleared && observeSiblingsPreserved)

end Flapjack.Test.PanBStateEmptyLocalsParity
