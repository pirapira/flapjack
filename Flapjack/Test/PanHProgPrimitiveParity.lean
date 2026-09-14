import Flapjack.PanHProgPrimitive

/-!
# Parity checks for Pancake `h_prog_primitive_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_primitive_probe.out` is generated from
`pan_itreeSemScript.sml:264-275`.  Lean checks cover primitive success,
primitive rejection, missing expression evaluation, and destination-shape
failure.
-/

namespace Flapjack.Test.PanHProgPrimitiveParity

open Flapjack

def primitive : PanPrimitiveHandler Nat
  | .addCarry, [.word left, .word right, .word carry] =>
      some (.rStruct [.word (left + right + (if carry == 0 then 0 else 1)), .word 0])
  | _, _ => none

def valid (_state : Nat) (name : VarName) (value : PanValue Nat) : Bool :=
  name == "dst" && match value with
  | .rStruct [.word _, .word _] => true
  | _ => false

def setVar (_state : Nat) (_name : VarName) (value : PanValue Nat) : Nat :=
  match value with
  | .rStruct [.word result, .word _] => result
  | _ => 0

def words (left right carry : Nat) : List (Option (PanValue Nat)) :=
  [some (.word left), some (.word right), some (.word carry)]

def observeSuccess : Bool :=
  match panHProgPrimitive 0 primitive valid setVar "dst" .addCarry (words 40 50 0) with
  | .ret (.normal state) => state == 90
  | _ => false

def observePrimitiveError : Bool :=
  match panHProgPrimitive 0 primitive valid setVar "dst" .addCarry
      [some (.word 40), some (.word 50)] with
  | .ret (.error state) => state == 0
  | _ => false

def observeMissingOperand : Bool :=
  match panHProgPrimitive 0 primitive valid setVar "dst" .addCarry
      [some (.word 40), none, some (.word 0)] with
  | .ret (.error state) => state == 0
  | _ => false

def observeShapeError : Bool :=
  match panHProgPrimitive 0 primitive valid setVar "other" .addCarry (words 40 50 0) with
  | .ret (.error state) => state == 0
  | _ => false

#guard observeSuccess
#guard observePrimitiveError
#guard observeMissingOperand
#guard observeShapeError

def runChecks : IO Bool := do
  if observeSuccess then IO.println "PASS h_prog_primitive success" else IO.println "FAIL h_prog_primitive success"
  if observePrimitiveError then IO.println "PASS h_prog_primitive primitive error" else IO.println "FAIL h_prog_primitive primitive error"
  if observeMissingOperand then IO.println "PASS h_prog_primitive missing operand" else IO.println "FAIL h_prog_primitive missing operand"
  if observeShapeError then IO.println "PASS h_prog_primitive shape error" else IO.println "FAIL h_prog_primitive shape error"
  pure (observeSuccess && observePrimitiveError && observeMissingOperand && observeShapeError)

end Flapjack.Test.PanHProgPrimitiveParity
