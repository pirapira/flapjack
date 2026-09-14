import Flapjack.CrepEval
import Flapjack.Test.CrepeSemantics

/-!
# Parity checks for `crepSem$eval_def`

The direct HOL fixture covers the source constant, local, memory, global, and
address expression cases.  The Lean checks exercise the corresponding hit
and miss behavior at the source-shaped runtime boundary.
-/

namespace Flapjack.Test.CrepEvalParity

open Flapjack

def hitState : CrepRuntimeState Nat Unit :=
  { crepeRuntimeState with
    locals := fun name => if name == 1 then some 7 else none
    memory := fun address => if address == 3 then some 9 else none
    memaddrs := fun address => address == 3
    globals := fun address => if address == 4 then some 11 else none
    baseAddress := 12
    topAddress := 13 }

def constant : Bool :=
  crepSemEvalExp hitState (.const 5) == some 5

def localHit : Bool :=
  crepSemEvalExp hitState (.var 1) == some 7

def localMiss : Bool :=
  crepSemEvalExp hitState (.var 2) == none

def memoryHit : Bool :=
  crepSemEvalExp hitState (.load (.const 3)) == some 9

def memoryMiss : Bool :=
  crepSemEvalExp hitState (.load (.const 8)) == none

def globalHit : Bool :=
  crepSemEvalExp hitState (.loadGlob 4) == some 11

def globalMiss : Bool :=
  crepSemEvalExp hitState (.loadGlob 8) == none

def addresses : Bool :=
  crepSemEvalExp hitState .baseAddr == some 12 &&
    crepSemEvalExp hitState .topAddr == some 13

#guard constant
#guard localHit
#guard localMiss
#guard memoryHit
#guard memoryMiss
#guard globalHit
#guard globalMiss
#guard addresses

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("eval constant", constant),
    ("eval local hit", localHit),
    ("eval local miss", localMiss),
    ("eval memory hit", memoryHit),
    ("eval memory miss", memoryMiss),
    ("eval global hit", globalHit),
    ("eval global miss", globalMiss),
    ("eval base/top addresses", addresses)]
  let results ← checks.mapM fun (name, passed) => do
    if passed then IO.println s!"PASS crep {name}"
    else IO.println s!"FAIL crep {name}"
    pure passed
  pure (results.all id)

end Flapjack.Test.CrepEvalParity
