import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the Pancake semantic `While` result

The source oracle is `scripts/hol-probes/pan_sem_while_error_probe.out`,
generated from `panSemScript.sml`. It pins four `While` outcomes against the
production evaluator:

* a non-word (unbound) condition is rejected with the explicit `SOME Error`
  result and the unchanged state;
* a zero condition exits normally at the same clock;
* a condition that stays nonzero runs until the clock is exhausted and ends in
  `SOME TimeOut` at clock zero;
* a body that clears the condition exits normally after one iteration,
  decrementing the clock once.
-/

namespace Flapjack.Test.PanSemWhileErrorParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def whileState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3))
      else if name == "c" then some (.word (BitVec.ofNat 64 1))
      else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def whileEvaluate (clock : Nat) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (whileState clock) program

def isErrorAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.error _ _ _ _), n), _) => n == clock
  | _ => false

def isNormalAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.control (.normal _ _ _ _), n), _) => n == clock
  | _ => false

def isTimeoutAt (clock : Nat)
    (result : Option
      (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) : Bool :=
  match result with
  | some ((.timeout _ _ _ _, n), _) => n == clock
  | _ => false

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def badWhile : Prog Word64 := .while (.var .local "z") .skip

def zeroWhile : Prog Word64 := .while (.const (BitVec.ofNat 64 0)) .skip

def timeoutWhile : Prog Word64 := .while (.const (BitVec.ofNat 64 1)) .skip

def oneIterWhile : Prog Word64 :=
  .while (.var .local "c") (.assign .local "c" (.const (BitVec.ofNat 64 0)))

def whileBadGuard : Bool :=
  isErrorAt 5 (whileEvaluate 5 badWhile) &&
    (match whileEvaluate 5 badWhile with
     | some ((.control (.error locals _ _ _), _), _) => isWordOption 3 (locals "x")
     | _ => false)

def whileZeroGuard : Bool := isNormalAt 5 (whileEvaluate 5 zeroWhile)

def whileTimeoutGuard : Bool := isTimeoutAt 0 (whileEvaluate 5 timeoutWhile)

def whileOneIterGuard : Bool :=
  isNormalAt 4 (whileEvaluate 5 oneIterWhile) &&
    (match whileEvaluate 5 oneIterWhile with
     | some ((.control (.normal locals _ _ _), _), _) => isWordOption 0 (locals "c")
     | _ => false)

def whileErrorGuard : Bool :=
  whileBadGuard && whileZeroGuard && whileTimeoutGuard && whileOneIterGuard

#guard whileErrorGuard

def runChecks : IO Bool := do
  if whileBadGuard then
    IO.println "PASS panSem While rejects non-word condition with Error and unchanged state"
  else IO.println "FAIL panSem While rejects non-word condition with Error and unchanged state"
  if whileZeroGuard then
    IO.println "PASS panSem While zero condition exits normally at same clock"
  else IO.println "FAIL panSem While zero condition exits normally at same clock"
  if whileTimeoutGuard then
    IO.println "PASS panSem While nonzero condition times out at clock zero"
  else IO.println "FAIL panSem While nonzero condition times out at clock zero"
  if whileOneIterGuard then
    IO.println "PASS panSem While cleared condition exits after one iteration"
  else IO.println "FAIL panSem While cleared condition exits after one iteration"
  pure whileErrorGuard

end Flapjack.Test.PanSemWhileErrorParity
