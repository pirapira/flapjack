import Flapjack.PanEval

/-!
# Parity checks for Pancake `eval_def`

The direct HOL fixture in `scripts/hol-probes/pan_eval_probe.out` is generated
from `pan_itreeSemScript.sml:79-158`.  Lean checks cover constants, local and
global lookup, structured field evaluation, and missing bindings.
-/

namespace Flapjack.Test.PanEvalParity

open Flapjack

def context : PanEvalContext Nat where
  structs := []
  locals := fun name => if name == "x" then some (.word 5) else none
  globals := fun name => if name == "g" then some (.word 6) else none
  memory := fun _ => none
  baseAddress := 10
  topAddress := 20
  bytesInWord := 8

def isWord (expected : Nat) : Option (PanValue Nat) → Bool
  | some (.word value) => value == expected
  | _ => false

def observeConst : Bool := isWord 7 (panEval context (.const 7))
def observeLocal : Bool := isWord 5 (panEval context (.var .local "x"))
def observeGlobal : Bool := isWord 6 (panEval context (.var .global "g"))
def observeField : Bool :=
  match panEval context (.rField 1 (.rStruct [.const 2, .const 9])) with
  | some (.word value) => value == 9
  | _ => false
def observeMissing : Bool := (panEval context (.var .local "missing")).isNone

#guard observeConst
#guard observeLocal
#guard observeGlobal
#guard observeField
#guard observeMissing

def runChecks : IO Bool := do
  if observeConst then IO.println "PASS eval constant" else IO.println "FAIL eval constant"
  if observeLocal then IO.println "PASS eval local" else IO.println "FAIL eval local"
  if observeGlobal then IO.println "PASS eval global" else IO.println "FAIL eval global"
  if observeField then IO.println "PASS eval structured field" else IO.println "FAIL eval structured field"
  if observeMissing then IO.println "PASS eval missing" else IO.println "FAIL eval missing"
  pure (observeConst && observeLocal && observeGlobal && observeField && observeMissing)

end Flapjack.Test.PanEvalParity
