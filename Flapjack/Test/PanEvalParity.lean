import Flapjack.PanEval
import Flapjack.Pancake.Semantics.PanSem

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

def structContext : PanEvalContext Nat where
  structs := [("Pair", { fields := [("left", Shape.one), ("right", Shape.one)],
                          size := 2 })]
  locals := fun _ => none
  globals := fun _ => none
  memory := fun _ => none
  baseAddress := 0
  topAddress := 0
  bytesInWord := 8

def isNamed (name : String) (arity : Nat) : Option (PanValue Nat) → Bool
  | some (.nStruct actual fields) => actual == name && fields.length == arity
  | _ => false

def observeNStruct : Bool :=
  isNamed "Pair" 2 (panEval structContext
    (.nStruct "Pair" [("left", .const 3), ("right", .const 4)]))

def observeNStructNameMismatch : Bool :=
  (panEval structContext
    (.nStruct "Pair" [("left", .const 3), ("bad", .const 4)])).isNone

def observeNStructShapeMismatch : Bool :=
  (panEval structContext
    (.nStruct "Pair" [("left", .const 3), ("right", .rStruct [])])).isNone

def observeMissingStruct : Bool :=
  (panEval context (.nStruct "Pair" [])).isNone

/-- The exact `word_lab` port and production `PanWordLab` are isomorphic. -/
theorem wordLabBridge (value : Nat) :
    (HolWordLab.word value).toPanWordLab.toHolWordLab = HolWordLab.word value :=
  HolWordLab.toPanWordLab_toHolWordLab _

def observeWordLabBridge : Bool :=
  (HolWordLab.word (3 : Nat)).toPanWordLab == PanWordLab.word 3

#guard observeConst
#guard observeLocal
#guard observeGlobal
#guard observeField
#guard observeMissing
#guard observeNStruct
#guard observeNStructNameMismatch
#guard observeNStructShapeMismatch
#guard observeMissingStruct
#guard observeWordLabBridge

def runChecks : IO Bool := do
  if observeConst then IO.println "PASS eval constant" else IO.println "FAIL eval constant"
  if observeLocal then IO.println "PASS eval local" else IO.println "FAIL eval local"
  if observeGlobal then IO.println "PASS eval global" else IO.println "FAIL eval global"
  if observeField then IO.println "PASS eval structured field" else IO.println "FAIL eval structured field"
  if observeMissing then IO.println "PASS eval missing" else IO.println "FAIL eval missing"
  if observeNStruct then IO.println "PASS eval NStruct" else IO.println "FAIL eval NStruct"
  if observeNStructNameMismatch then IO.println "PASS eval NStruct name mismatch"
    else IO.println "FAIL eval NStruct name mismatch"
  if observeNStructShapeMismatch then IO.println "PASS eval NStruct shape mismatch"
    else IO.println "FAIL eval NStruct shape mismatch"
  if observeMissingStruct then IO.println "PASS eval NStruct missing struct"
    else IO.println "FAIL eval NStruct missing struct"
  if observeWordLabBridge then IO.println "PASS eval word_lab bridge"
    else IO.println "FAIL eval word_lab bridge"
  pure (observeConst && observeLocal && observeGlobal && observeField && observeMissing &&
    observeNStruct && observeNStructNameMismatch && observeNStructShapeMismatch &&
    observeMissingStruct && observeWordLabBridge)

end Flapjack.Test.PanEvalParity
