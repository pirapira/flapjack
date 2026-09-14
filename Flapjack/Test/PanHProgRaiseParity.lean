import Flapjack.PanHProgRaise

/-!
# Parity checks for Pancake `h_prog_raise_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_raise_probe.out` is generated from
`pan_itreeSemScript.sml:445-454`.  Lean checks cover the valid exception
shape, missing/incorrect shape, oversized shape, and source-state projections.
-/

namespace Flapjack.Test.PanHProgRaiseParity

open Flapjack

def structs : StructContext := []
def largeValue : PanValue Nat := .rStruct (List.replicate 33 (.word 1))

def observeRaised : Bool :=
  match panHProgRaise structs 0 99 "E" (some .one) (some (.word 7)) with
  | .ret (.raised state exception (.word value)) =>
      state == 99 && exception == "E" && value == 7
  | _ => false

def observeInvalid : Bool :=
  match panHProgRaise structs 0 99 "E" none (some (.word 7)) with
  | .ret (.error state) => state == 0
  | _ => false

def observeWrongShape : Bool :=
  match panHProgRaise structs 0 99 "E" (some (.comb [])) (some (.word 7)) with
  | .ret (.error state) => state == 0
  | _ => false

def observeOversized : Bool :=
  match panHProgRaise structs 0 99 "E" (some (.comb (List.replicate 33 .one)))
      (some largeValue) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeRaised
#guard observeInvalid
#guard observeWrongShape
#guard observeOversized

def runChecks : IO Bool := do
  if observeRaised then IO.println "PASS h_prog_raise valid exception" else IO.println "FAIL h_prog_raise valid exception"
  if observeInvalid then IO.println "PASS h_prog_raise invalid lookup" else IO.println "FAIL h_prog_raise invalid lookup"
  if observeWrongShape then IO.println "PASS h_prog_raise wrong shape" else IO.println "FAIL h_prog_raise wrong shape"
  if observeOversized then IO.println "PASS h_prog_raise shape limit" else IO.println "FAIL h_prog_raise shape limit"
  pure (observeRaised && observeInvalid && observeWrongShape && observeOversized)

end Flapjack.Test.PanHProgRaiseParity
