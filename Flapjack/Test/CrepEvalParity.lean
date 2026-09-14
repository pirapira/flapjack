import Flapjack.CrepEval
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$eval_def`

The direct HOL fixture in `scripts/hol-probes/crep_eval_probe.out` evaluates
the original source definition over representative local/global/memory and
address state.  The executable checks exercise the corresponding Lean
boundary, including an intermediate word operation and a missing local.
-/

namespace Flapjack.Test.CrepEvalParity

open Flapjack

def globalsState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    globals := fun address => if address == 3 then some 9 else none }

def evalConst : Bool := crepEval crepeRuntimeState (.const 7) == some 7

def evalLocal : Bool := crepEval crepeRuntimeState (.var 1) == some 10

def evalMissing : Bool := crepEval crepeRuntimeState (.var 99) == none

def evalGlobal : Bool := crepEval globalsState (.loadGlob 3) == some 9

def evalLoad : Bool := crepEval crepeRuntimeState (.load (.const 10)) == some 7

def evalOp : Bool :=
  crepEval crepeRuntimeState (.op .add [.const 1, .const 2]) == some 3

def evalBaseTop : Bool :=
  crepEval crepeRuntimeState .baseAddr == some 0 &&
    crepEval crepeRuntimeState .topAddr == some 100

#guard evalConst
#guard evalLocal
#guard evalMissing
#guard evalGlobal
#guard evalLoad
#guard evalOp
#guard evalBaseTop

def runChecks : IO Bool := do
  if evalConst then IO.println "PASS crep eval constant"
  else IO.println "FAIL crep eval constant"
  if evalLocal then IO.println "PASS crep eval local"
  else IO.println "FAIL crep eval local"
  if evalMissing then IO.println "PASS crep eval missing local"
  else IO.println "FAIL crep eval missing local"
  if evalGlobal then IO.println "PASS crep eval global"
  else IO.println "FAIL crep eval global"
  if evalLoad then IO.println "PASS crep eval memory load"
  else IO.println "FAIL crep eval memory load"
  if evalOp then IO.println "PASS crep eval word operation"
  else IO.println "FAIL crep eval word operation"
  if evalBaseTop then IO.println "PASS crep eval base/top addresses"
  else IO.println "FAIL crep eval base/top addresses"
  pure (evalConst && evalLocal && evalMissing && evalGlobal && evalLoad &&
    evalOp && evalBaseTop)

end Flapjack.Test.CrepEvalParity
