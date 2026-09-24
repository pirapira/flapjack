import Flapjack.Pancake.Semantics.PanSem.Total
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the HOL-shaped total `evaluate` base cases

The source oracles are `scripts/hol-probes/pan_sem_skip_e2e_probe.out`
(`skip_result=NONE`, `skip_clock=5`, `skip_locals_preserved=SOME (ValWord 7w)`)
and `scripts/hol-probes/pan_sem_tick_e2e_probe.out` (`tick_zero_result=SOME
TimeOut`, `tick_zero_clock=0`, `tick_zero_locals_cleared=NONE`,
`tick_succ_result=NONE`, `tick_succ_clock=4`, `tick_succ_locals_preserved=SOME
(ValWord 7w)`).

This pins the executed source evaluator's `(result, state)` projection against
the total HOL-shaped base cases:

* `Skip` completes normally with the state carried verbatim;
* `Tick` at clock zero is a timeout with cleared locals;
* `Tick` above clock zero decrements the clock and preserves the locals.
-/

namespace Flapjack.Test.PanSemTotalParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def totalState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 7)) else none
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

def totalEvaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) state program).map panSemTotalOfExecuted

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def skipGuard : Bool :=
  match totalEvaluate (totalState 5) (.skip : Prog Word64) with
  | some (.normal, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def tickSuccGuard : Bool :=
  match totalEvaluate (totalState 5) (.tick : Prog Word64) with
  | some (.normal, state) => state.clock == 4 && isWordOption 7 (state.locals "x")
  | _ => false

def tickZeroGuard : Bool :=
  match totalEvaluate (totalState 0) (.tick : Prog Word64) with
  | some (.timeout, state) => state.clock == 0 && (state.locals "x").isNone
  | _ => false

def totalGuard : Bool := skipGuard && tickSuccGuard && tickZeroGuard

#guard totalGuard

example :
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.skip : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateSkip (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_skip_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

example :
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.tick : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateTick (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_tick_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

def runChecks : IO Bool := do
  if skipGuard then
    IO.println "PASS panSem total Skip carries the state verbatim"
  else IO.println "FAIL panSem total Skip carries the state verbatim"
  if tickSuccGuard then
    IO.println "PASS panSem total Tick decrements the clock and preserves locals"
  else IO.println "FAIL panSem total Tick decrements the clock and preserves locals"
  if tickZeroGuard then
    IO.println "PASS panSem total Tick timeout clears locals at clock zero"
  else IO.println "FAIL panSem total Tick timeout clears locals at clock zero"
  pure totalGuard

end Flapjack.Test.PanSemTotalParity
