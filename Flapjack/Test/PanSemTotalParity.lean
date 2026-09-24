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

/-- The compositional HOL `Seq` step applied to base-case first-command results
    (this is not a whole-program evaluator): compile `Skip ; Skip` by pairing the
    `Skip` base case with a `Skip` continuation. -/
def seqStepSkipSkip : PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  let first := panSemEvaluateSkip (totalState 5)
  panSemTotalSeqStep 5 first.1 first.2 panSemEvaluateSkip

def seqNormalGuard : Bool :=
  match seqStepSkipSkip with
  | (.normal, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

/-- `Tick ; Skip`: the first base case decrements the clock to 4, and the `Seq`
    step clamps the entry clock to it before running the continuation. -/
def seqStepTickSkip : PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  let first := panSemEvaluateTick (totalState 5)
  panSemTotalSeqStep 5 first.1 first.2 panSemEvaluateSkip

def seqTickGuard : Bool :=
  match seqStepTickSkip with
  | (.normal, state) => state.clock == 4 && isWordOption 7 (state.locals "x")
  | _ => false

/-- A continuation that would be observable if it were (wrongly) run. -/
def seqObservableContinuation
    (_ : PanSemState Word64 (FfiState Unit)) :
    PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  (.error, totalState 5)

def seqStepBreak : PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  panSemTotalSeqStep 5 .broke (totalState 5) seqObservableContinuation

def seqBreakGuard : Bool :=
  match seqStepBreak with
  | (.broke, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def seqStepContinue : PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  panSemTotalSeqStep 5 .continued (totalState 5) seqObservableContinuation

def seqContinueGuard : Bool :=
  match seqStepContinue with
  | (.continued, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

/-- A state whose global `g` is bound, for the global-assignment case. -/
def totalAssignState : PanSemState Word64 (FfiState Unit) :=
  { totalState 5 with
    globals := fun name =>
      if name == "g" then some (.word (BitVec.ofNat 64 4)) else none }

def totalAssignEvaluate (state : PanSemState Word64 (FfiState Unit)) (kind : VarKind)
    (name : VarName) (value : Exp Word64) :
    PanSemProgResult Word64 Unit × PanSemState Word64 (FfiState Unit) :=
  panSemTotalAssign (BitVec.ofNat 64 8) state kind name value

def assignLocalGuard : Bool :=
  match totalAssignEvaluate (totalState 5) .local "x" (.const (BitVec.ofNat 64 9)) with
  | (.normal, state) => state.clock == 5 && isWordOption 9 (state.locals "x")
  | _ => false

def assignGlobalGuard : Bool :=
  match totalAssignEvaluate totalAssignState .global "g" (.const (BitVec.ofNat 64 9)) with
  | (.normal, state) => state.clock == 5 && isWordOption 9 (state.globals "g")
  | _ => false

def assignFreshGuard : Bool :=
  match totalAssignEvaluate (totalState 5) .local "y" (.const (BitVec.ofNat 64 9)) with
  | (.error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def assignMissingGuard : Bool :=
  match totalAssignEvaluate (totalState 5) .local "x" (.var .local "z") with
  | (.error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalGuard : Bool :=
  skipGuard && tickSuccGuard && tickZeroGuard && seqNormalGuard && seqBreakGuard &&
    seqContinueGuard && seqTickGuard && assignLocalGuard && assignGlobalGuard &&
    assignFreshGuard && assignMissingGuard

#guard totalGuard

example :
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.skip : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateSkip (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_skip_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

example :
    panSemTotalSeqStep 5 (.normal : PanSemProgResult Word64 Unit) (totalState 5)
        panSemEvaluateSkip =
      panSemEvaluateSkip (panSemFixClock 5 (totalState 5)) :=
  panSemTotalSeqStep_normal 5 (totalState 5) panSemEvaluateSkip

example :
    panSemTotalSeqStep 5 (.broke : PanSemProgResult Word64 Unit) (totalState 5)
        seqObservableContinuation =
      (.broke, panSemFixClock 5 (totalState 5)) :=
  panSemTotalSeqStep_of_ne_normal 5 .broke (totalState 5) seqObservableContinuation
    (by intro h; cases h)

example :
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.tick : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateTick (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_tick_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

example :
    (panSemEvaluateCodeStateWithFuel statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) 4 (totalState 5)
        (.assign .local "x" (.const (BitVec.ofNat 64 9)) : Prog Word64)).map
        (fun result =>
          panSemTotalOfExecuted (result, panSemCodeStateAfter (totalState 5) result)) =
      some (panSemTotalAssign (BitVec.ofNat 64 8) (totalState 5) .local "x"
        (.const (BitVec.ofNat 64 9))) :=
  panSemEvaluateCodeStateWithFuel_assign_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) 3 (totalState 5) .local "x"
    (.const (BitVec.ofNat 64 9))

example :
    panSemTotalAssignStep (totalState 5) .local "x" (.word (BitVec.ofNat 64 9)) =
      (.normal,
        { totalState 5 with
          locals := updatePanValueMap (totalState 5).locals "x" (.word (BitVec.ofNat 64 9)) }) :=
  panSemTotalAssignStep_normal_local (totalState 5) "x" (.word (BitVec.ofNat 64 9))
    (by simp [panValueAssignmentValid, panValueShape, panShapeMatches, totalState])

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
  if seqNormalGuard then
    IO.println "PASS panSem total Seq Skip/Skip completes normally"
  else IO.println "FAIL panSem total Seq Skip/Skip completes normally"
  if seqBreakGuard then
    IO.println "PASS panSem total Seq Break short-circuits and skips the second command"
  else IO.println "FAIL panSem total Seq Break short-circuits and skips the second command"
  if seqContinueGuard then
    IO.println "PASS panSem total Seq Continue short-circuits and skips the second command"
  else IO.println "FAIL panSem total Seq Continue short-circuits and skips the second command"
  if seqTickGuard then
    IO.println "PASS panSem total Seq Tick clamps the clock before the second command"
  else IO.println "FAIL panSem total Seq Tick clamps the clock before the second command"
  if assignLocalGuard then
    IO.println "PASS panSem total Assign accepted local writes the bound value"
  else IO.println "FAIL panSem total Assign accepted local writes the bound value"
  if assignGlobalGuard then
    IO.println "PASS panSem total Assign accepted global writes the bound value"
  else IO.println "FAIL panSem total Assign accepted global writes the bound value"
  if assignFreshGuard then
    IO.println "PASS panSem total Assign fresh destination rejected with Error and unchanged state"
  else IO.println "FAIL panSem total Assign fresh destination rejected with Error and unchanged state"
  if assignMissingGuard then
    IO.println "PASS panSem total Assign missing source rejected with Error and unchanged state"
  else IO.println "FAIL panSem total Assign missing source rejected with Error and unchanged state"
  pure totalGuard

end Flapjack.Test.PanSemTotalParity
