import Flapjack.CrepEvaluate

/-!
# Parity checks for Crepe `evaluate_def`

The direct HOL fixture in `scripts/hol-probes/crep_evaluate_probe.out` is
generated from `crepSemScript.sml:240-446`.  The checks cover normal execution,
an intermediate assignment in a sequence, return values, a control result,
and a failing expression, while also checking the state carried by normal
and returned results.
-/

namespace Flapjack.Test.CrepEvaluateParity

open Flapjack

def primitive : CrepPrimitiveHandler Nat := fun _ _ => none
def ffi : CrepFfiHandler Nat := noCrepFfi Nat
def sharedMem : CrepSharedMemHandler Nat := defaultCrepSharedMemHandler

def sourceState : CrepState Nat where
  locals := fun name => if name == 0 then some 7 else none
  memory := fun address => if address == 8 then some 9 else none
  globals := fun address => if address == 3 then some 5 else none

def evaluateSkip : Bool :=
  match crepEvaluate [] primitive ffi sharedMem 100 200 3 sourceState .skip with
  | some (.normal state) =>
      state.locals 0 == some 7 && state.memory 8 == some 9 &&
        state.globals 3 == some 5
  | _ => false

def evaluateAssignReturn : Bool :=
  let program : CrepProg Nat :=
    .seq (.assign 0 (.const 3)) (.return [.var 0])
  match crepEvaluate [] primitive ffi sharedMem 100 200 5 sourceState program with
  | some (.returned state [value]) =>
      value == 3 && state.locals 0 == some 3 &&
        state.memory 8 == some 9 && state.globals 3 == some 5
  | _ => false

def evaluateBreak : Bool :=
  match crepEvaluate [] primitive ffi sharedMem 100 200 2 sourceState (.break 3) with
  | some (.broke state 3) => state.locals 0 == some 7
  | _ => false

def evaluateMissing : Bool :=
  match crepEvaluate [] primitive ffi sharedMem 100 200 2 sourceState
      (.return [.var 99]) with
  | none => true
  | _ => false

#guard evaluateSkip
#guard evaluateAssignReturn
#guard evaluateBreak
#guard evaluateMissing

def runChecks : IO Bool := do
  if evaluateSkip then IO.println "PASS crep evaluate Skip preserves state"
  else IO.println "FAIL crep evaluate Skip preserves state"
  if evaluateAssignReturn then
    IO.println "PASS crep evaluate sequence assignment and Return"
  else
    IO.println "FAIL crep evaluate sequence assignment and Return"
  if evaluateBreak then IO.println "PASS crep evaluate Break result"
  else IO.println "FAIL crep evaluate Break result"
  if evaluateMissing then IO.println "PASS crep evaluate missing expression fails"
  else IO.println "FAIL crep evaluate missing expression fails"
  pure (evaluateSkip && evaluateAssignReturn && evaluateBreak && evaluateMissing)

end Flapjack.Test.CrepEvaluateParity
