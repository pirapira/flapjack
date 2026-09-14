import Flapjack.PanEmptyLocals

/-!
# Parity checks for Pancake `empty_locals_def`

The direct HOL fixture in `scripts/hol-probes/pan_empty_locals_probe.out`
evaluates the source record update.  The Lean checks exercise both the cleared
locals and representative untouched state components.
-/

namespace Flapjack.Test.PanEmptyLocalsParity

open Flapjack

def sourceState : PanSemState Nat String where
  locals := updatePanValueMap (fun _ => none) "x" (.word 3)
  globals := updatePanValueMap (fun _ => none) "g" (.word 5)
  structs := []
  code := fun _ => none
  exceptionShapes := fun _ => none
  memory := fun address => if address == 7 then some (.word 9) else none
  memaddrs := fun address => address == 7
  sharedMemaddrs := fun _ => false
  clock := 12
  be := true
  ffi := "ffi"
  baseAddress := 100
  topAddress := 200

def observeLocalsCleared : Bool :=
  ((panEmptyLocals sourceState).locals "x").isNone &&
    ((panEmptyLocals sourceState).locals "other").isNone

def observeSiblingsPreserved : Bool :=
  ((panEmptyLocals sourceState).globals "g").isSome &&
    ((panEmptyLocals sourceState).memory 7).isSome &&
    (panEmptyLocals sourceState).clock == 12 &&
    (panEmptyLocals sourceState).baseAddress == 100 &&
    (panEmptyLocals sourceState).topAddress == 200

#guard observeLocalsCleared
#guard observeSiblingsPreserved

def runChecks : IO Bool := do
  if observeLocalsCleared then IO.println "PASS empty_locals clears locals"
  else IO.println "FAIL empty_locals clears locals"
  if observeSiblingsPreserved then IO.println "PASS empty_locals preserves siblings"
  else IO.println "FAIL empty_locals preserves siblings"
  pure (observeLocalsCleared && observeSiblingsPreserved)

end Flapjack.Test.PanEmptyLocalsParity
