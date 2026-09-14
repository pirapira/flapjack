import Flapjack.PanEvaluate
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for Pancake `evaluate_def`

The source oracle is `scripts/hol-probes/pan_sem_e2e_probe.out`, generated
from `panSemScript.sml:556-736`.  Its `return_41`, `return_mul_42`, and
`return_if_13` observations are direct HOL evaluations of
`FST (panSem$evaluate ...)`; the call, memory, and FFI fixtures use the same
source boundary.  These checks exercise the source-shaped wrapper on a
constant return, an intermediate clocked sequence, a zero-clock timeout, and
a function call with argument transfer and return-shape contracts.
-/

namespace Flapjack.Test.PanEvaluateParity

open Flapjack
open Flapjack.RiscV

def emptyPanState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { structs := []
    functions := []
    locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8 }

def evaluateSkip :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.skip : Prog (Word 64))

def evaluateReturn41 :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 4) (.return (.const (BitVec.ofNat 64 41)) : Prog (Word 64))

def evaluateSequence :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 1)
    ((.seq .tick (.return (.const (BitVec.ofNat 64 13)))) : Prog (Word 64))

def evaluateTickAtZero :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (emptyPanState 0) (.tick : Prog (Word 64))

def idFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("id", ["x"], .return (.var .local "x"))]

def idContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("id", .one)] [] [("id", [("x", .one)])]

def evaluateCall :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    ({ emptyPanState 10 with
        functions := idFunctions
        contracts := some idContracts }
      : PanSemEvaluateState (Word 64) Unit)
    (.call none "id" [.const (BitVec.ofNat 64 7)] : Prog (Word 64))

def isWord (expected : Nat) : PanValue (Word 64) → Bool
  | .word value => value == BitVec.ofNat 64 expected
  | _ => false

def observeSkip : Bool :=
  match evaluateSkip with
  | some (.control (.normal locals _ _ _), 4) => locals "x" = none
  | _ => false

def observeReturn41 : Bool :=
  match evaluateReturn41 with
  | some (.control (.returned locals _ _ _ [value]), 4) =>
      locals "x" = none && isWord 41 value
  | _ => false

def observeSequence : Bool :=
  match evaluateSequence with
  | some (.control (.returned _ _ _ _ [value]), 0) => isWord 13 value
  | _ => false

def observeTickAtZero : Bool :=
  match evaluateTickAtZero with
  | some (.timeout locals _ _ _, 0) => locals "x" = none
  | _ => false

def observeCall : Bool :=
  match evaluateCall with
  | some (.control (.returned locals _ _ _ [value]), 9) =>
      locals "x" = none && isWord 7 value
  | _ => false

#guard observeSkip
#guard observeReturn41
#guard observeSequence
#guard observeTickAtZero
#guard observeCall

def runChecks : IO Bool := do
  if observeSkip then IO.println "PASS evaluate skip" else IO.println "FAIL evaluate skip"
  if observeReturn41 then IO.println "PASS evaluate return_41" else IO.println "FAIL evaluate return_41"
  if observeSequence then IO.println "PASS evaluate sequence" else IO.println "FAIL evaluate sequence"
  if observeTickAtZero then IO.println "PASS evaluate timeout" else IO.println "FAIL evaluate timeout"
  if observeCall then IO.println "PASS evaluate call_id_7" else IO.println "FAIL evaluate call_id_7"
  pure (observeSkip && observeReturn41 && observeSequence && observeTickAtZero && observeCall)

end Flapjack.Test.PanEvaluateParity
