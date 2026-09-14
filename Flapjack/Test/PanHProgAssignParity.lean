import Flapjack.PanHProgAssign

/-!
# Parity checks for Pancake `h_prog_assign_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_assign_probe.out` comes from
`pan_itreeSemScript.sml:254-275`.  These checks cover a valid local update,
invalid destination/value validation, and failed expression evaluation.
-/

namespace Flapjack.Test.PanHProgAssignParity

open Flapjack

def evalValue : Nat → Exp Nat → Option (PanValue Nat)
  | _, .const value => some (.word value)
  | _, .rStruct [] => some (.rStruct [])
  | _, _ => none

def isValid : Nat → VarKind → VarName → PanValue Nat → Bool
  | _, .local, "x", .word _ => true
  | _, _, _, _ => false

def setValue : Nat → VarKind → VarName → PanValue Nat → Nat
  | state, _, _, .word value => state + value
  | state, _, _, _ => state

def observeValid : Bool :=
  match panHProgAssign 0 evalValue isValid setValue .local "x" (.const 7) with
  | .ret (.normal state) => state == 7
  | _ => false

def observeInvalidDestination : Bool :=
  match panHProgAssign 0 evalValue isValid setValue .local "missing" (.const 7) with
  | .ret (.error state) => state == 0
  | _ => false

def observeInvalidValue : Bool :=
  match panHProgAssign 0 evalValue isValid setValue .local "x" (.rStruct []) with
  | .ret (.error state) => state == 0
  | _ => false

def observeFailedEval : Bool :=
  match panHProgAssign 0 evalValue isValid setValue .local "x"
      (.var .local "missing") with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeValid
#guard observeInvalidDestination
#guard observeInvalidValue
#guard observeFailedEval

def runChecks : IO Bool := do
  if observeValid then IO.println "PASS h_prog_assign valid local" else IO.println "FAIL h_prog_assign valid local"
  if observeInvalidDestination then IO.println "PASS h_prog_assign invalid destination" else IO.println "FAIL h_prog_assign invalid destination"
  if observeInvalidValue then IO.println "PASS h_prog_assign invalid value" else IO.println "FAIL h_prog_assign invalid value"
  if observeFailedEval then IO.println "PASS h_prog_assign failed evaluation" else IO.println "FAIL h_prog_assign failed evaluation"
  pure (observeValid && observeInvalidDestination && observeInvalidValue && observeFailedEval)

end Flapjack.Test.PanHProgAssignParity
