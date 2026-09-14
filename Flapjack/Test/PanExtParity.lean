import Flapjack.PanExt

/-!
# Parity checks for Pancake `ext_def`

The direct HOL fixture in `scripts/hol-probes/pan_ext_probe.out` is generated
from `pan_itreeSemScript.sml:625-642`.  Lean checks cover replacement of the
FFI field, replacement of the clock, and preservation of an unrelated field.
-/

namespace Flapjack.Test.PanExtParity

open Flapjack

structure State where
  clock : Nat
  ffi : Nat
  other : Nat

def setFfi (state : State) (ffi : Nat) : State :=
  { state with ffi := ffi }

def setClock (state : State) (clock : Nat) : State :=
  { state with clock := clock }

def observeFfi : Bool :=
  (panExt { clock := 7, ffi := 3, other := 11 } 19 23 setFfi setClock).ffi == 23

def observeClock : Bool :=
  (panExt { clock := 7, ffi := 3, other := 11 } 19 23 setFfi setClock).clock == 19

def observeOther : Bool :=
  (panExt { clock := 7, ffi := 3, other := 11 } 19 23 setFfi setClock).other == 11

#guard observeFfi
#guard observeClock
#guard observeOther

def runChecks : IO Bool := do
  if observeFfi then IO.println "PASS ext ffi replacement" else IO.println "FAIL ext ffi replacement"
  if observeClock then IO.println "PASS ext clock replacement" else IO.println "FAIL ext clock replacement"
  if observeOther then IO.println "PASS ext unrelated field" else IO.println "FAIL ext unrelated field"
  pure (observeFfi && observeClock && observeOther)

end Flapjack.Test.PanExtParity
