import Flapjack.PanValues

/-!
# Original-domain parity for `panSem.upd_locals_def`

The direct HOL fixture in `scripts/hol-probes/pan_upd_locals_probe.out` is
generated from `cakeml/pancake/semantics/panSemScript.sml:431-434`.  The Lean
checks exercise duplicate binding order and the empty argument case.
-/

namespace Flapjack.Test.PanUpdLocalsParity

open Flapjack

def duplicateBinding : Bool :=
  match bindPanValueParameters ["x", "x"]
      [(.word 3 : PanValue Nat), .word 7] with
  | some locals =>
      match locals "x" with
      | some (.word value) => value == 7
      | _ => false
  | none => false

def emptyBinding : Bool :=
  match bindPanValueParameters ([] : List String) ([] : List (PanValue Nat)) with
  | some locals => (locals "x").isNone
  | none => false

#guard duplicateBinding
#guard emptyBinding

def runChecks : IO Bool := do
  if duplicateBinding then IO.println "PASS Pan upd_locals duplicate last-wins" else
    IO.println "FAIL Pan upd_locals duplicate last-wins"
  if emptyBinding then IO.println "PASS Pan upd_locals empty" else
    IO.println "FAIL Pan upd_locals empty"
  pure (duplicateBinding && emptyBinding)

end Flapjack.Test.PanUpdLocalsParity
