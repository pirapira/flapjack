import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for Pancake `crepSem.evaluate_def`

The direct HOL fixture in
`scripts/hol-probes/crep_evaluate_probe.out` is generated from
`cakeml/pancake/semantics/crepSemScript.sml:240-389`.  The checks below
exercise the corresponding runtime boundary and compare result, locals, and
clock with the source observations.  The sequence case also checks that the
assignment is an intermediate state before `Return` clears locals.
-/

namespace Flapjack.Test.CrepEvaluateParity

open Flapjack

def assignProgram : CrepProg Nat :=
  .assign 1 (.const 7)

def sequenceReturnProgram : CrepProg Nat :=
  .seq (.assign 1 (.const 7)) (.return [.var 1])

def evaluateSkip : Bool :=
  match evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2 crepeRuntimeState .skip with
  | some (.normal, state) => state.clock == 10
  | _ => false

def evaluateAssign : Bool :=
  match evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2 { crepeRuntimeState with clock := 5 }
      assignProgram with
  | some (.normal, state) => state.locals 1 == some 7 && state.clock == 5
  | _ => false

def evaluateSequenceReturn : Bool :=
  match evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 4
      { crepeRuntimeState with
        locals := fun name => if name == 1 then some 0 else none,
        clock := 5 }
      sequenceReturnProgram with
  | some (.returned [7], state) => state.locals 1 == none && state.clock == 5
  | _ => false

def evaluateTickTimeout : Bool :=
  match evalCrepRuntimeResult crepeRuntimeSharedHandler
      crepeSemanticsPrimitive 2
      { crepeRuntimeState with clock := 0 }
      .tick with
  | some (.timeout, state) => state.locals 1 == none && state.clock == 0
  | _ => false

#guard evaluateSkip
#guard evaluateAssign
#guard evaluateSequenceReturn
#guard evaluateTickTimeout

def runChecks : IO Bool := do
  if evaluateSkip then IO.println "PASS crep evaluate Skip" else
    IO.println "FAIL crep evaluate Skip"
  if evaluateAssign then IO.println "PASS crep evaluate Assign" else
    IO.println "FAIL crep evaluate Assign"
  if evaluateSequenceReturn then IO.println "PASS crep evaluate Seq/Return" else
    IO.println "FAIL crep evaluate Seq/Return"
  if evaluateTickTimeout then IO.println "PASS crep evaluate Tick timeout" else
    IO.println "FAIL crep evaluate Tick timeout"
  pure (evaluateSkip && evaluateAssign && evaluateSequenceReturn &&
    evaluateTickTimeout)

end Flapjack.Test.CrepEvaluateParity
