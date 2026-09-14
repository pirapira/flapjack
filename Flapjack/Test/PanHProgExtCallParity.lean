import Flapjack.PanHProgExtCall

/-!
# Parity checks for Pancake `h_prog_ext_call_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_ext_call_probe.out` is generated from
`pan_itreeSemScript.sml:415-443`.  Lean checks cover nonempty/empty names,
invalid byte arrays, equal-length return writes, mismatch, and final outcomes.
-/

namespace Flapjack.Test.PanHProgExtCallParity

open Flapjack

def writeArray : Nat → List UInt8 → Nat := fun _ bytes => bytes.length

def callTree : PanFfiTree (PanHProgExtCallResult Nat) :=
  panHProgExtCall 0 99 writeArray "foo" (some [1, 2]) (some [3, 4])

def emptyTree : PanFfiTree (PanHProgExtCallResult Nat) :=
  panHProgExtCall 0 99 writeArray "" (some [1, 2]) (some [3, 4])

def invalidTree : PanFfiTree (PanHProgExtCallResult Nat) :=
  panHProgExtCall 0 99 writeArray "foo" none (some [3, 4])

def returningWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [5, 6], state := 0 }

def shortWorld : PanFfiWorld Nat :=
  { oracle := fun _ state _ _bytes => .returned state [5], state := 0 }

def finalWorld : PanFfiWorld Nat :=
  { oracle := fun _ _ _ _ => .final .failed, state := 0 }

def observeEvent : Bool :=
  match callTree with
  | .vis (.extCall "foo") [1, 2] [3, 4] _ => true
  | _ => false

def observeEmpty : Bool :=
  match emptyTree with
  | .ret (.normal state) => state == 2
  | _ => false

def observeInvalid : Bool :=
  match invalidTree with
  | .ret (.error state) => state == 0
  | _ => false

def observeReturn : Bool :=
  match compFfi 1 callTree returningWorld with
  | some (.ret (.normal state), world) => state == 2 && world.state == 0
  | _ => false

def observeMismatch : Bool :=
  match compFfi 1 callTree shortWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 99 && event.name == .extCall "foo" && event.outcome == .failed
  | _ => false

def observeFinal : Bool :=
  match compFfi 1 callTree finalWorld with
  | some (.ret (.finalFfi state event), _) =>
      state == 99 && event.name == .extCall "foo" && event.outcome == .failed
  | _ => false

#guard observeEvent
#guard observeEmpty
#guard observeInvalid
#guard observeReturn
#guard observeMismatch
#guard observeFinal

def runChecks : IO Bool := do
  if observeEvent then IO.println "PASS h_prog_ext_call event" else IO.println "FAIL h_prog_ext_call event"
  if observeEmpty then IO.println "PASS h_prog_ext_call empty name" else IO.println "FAIL h_prog_ext_call empty name"
  if observeInvalid then IO.println "PASS h_prog_ext_call invalid bytes" else IO.println "FAIL h_prog_ext_call invalid bytes"
  if observeReturn then IO.println "PASS h_prog_ext_call Oracle_return" else IO.println "FAIL h_prog_ext_call Oracle_return"
  if observeMismatch then IO.println "PASS h_prog_ext_call length failure" else IO.println "FAIL h_prog_ext_call length failure"
  if observeFinal then IO.println "PASS h_prog_ext_call Oracle_final" else IO.println "FAIL h_prog_ext_call Oracle_final"
  pure (observeEvent && observeEmpty && observeInvalid && observeReturn &&
    observeMismatch && observeFinal)

end Flapjack.Test.PanHProgExtCallParity
