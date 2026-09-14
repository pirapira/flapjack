import Flapjack.PanHProgReturn

/-!
# Parity checks for Pancake `h_prog_return_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_return_probe.out` is generated from
`pan_itreeSemScript.sml:456-464`.  The Lean checks cover successful return
with cleared-state projection, missing evaluation, and the source 32-word
shape limit.
-/

namespace Flapjack.Test.PanHProgReturnParity

open Flapjack

def structs : StructContext := []
def largeValue : PanValue Nat := .rStruct (List.replicate 33 (.word 1))

def observeReturn : Bool :=
  match panHProgReturn structs 0 99 (some (.word 7)) with
  | .ret (.returned state (.word value)) => state == 99 && value == 7
  | _ => false

def observeInvalid : Bool :=
  match panHProgReturn (α := Nat) structs 0 99 none with
  | .ret (.error state) => state == 0
  | _ => false

def observeOversized : Bool :=
  match panHProgReturn structs 0 99 (some largeValue) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeReturn
#guard observeInvalid
#guard observeOversized

def runChecks : IO Bool := do
  if observeReturn then IO.println "PASS h_prog_return valid value" else IO.println "FAIL h_prog_return valid value"
  if observeInvalid then IO.println "PASS h_prog_return invalid evaluation" else IO.println "FAIL h_prog_return invalid evaluation"
  if observeOversized then IO.println "PASS h_prog_return shape limit" else IO.println "FAIL h_prog_return shape limit"
  pure (observeReturn && observeInvalid && observeOversized)

end Flapjack.Test.PanHProgReturnParity
