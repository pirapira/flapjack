import Flapjack.Pancake.Semantics.PanSem.Total
import Flapjack.Pancake.Semantics.PanSem.TotalMeasure
import Flapjack.Pancake.Semantics.PanSem.TotalMeasureIf
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the total PanSem clock-leaf evaluator

The source oracles are `scripts/hol-probes/pan_sem_skip_e2e_probe.out`
(`skip_result=NONE`, `skip_clock=5`, `skip_locals_preserved=SOME (ValWord 7w)`)
and `scripts/hol-probes/pan_sem_tick_e2e_probe.out` (`tick_zero_result=SOME
TimeOut`, `tick_zero_clock=0`, `tick_zero_locals_cleared=NONE`,
`tick_succ_result=NONE`, `tick_succ_clock=4`, `tick_succ_locals_preserved=SOME
(ValWord 7w)`), plus `scripts/hol-probes/pan_sem_break_continue_e2e_probe.out`
(`break_result=SOME Break`, `continue_result=SOME Continue`, and both preserve
the clock and local binding).

This pins the executed source evaluator's `(result, state)` projection against
the total HOL-shaped base cases:

* `Skip` completes normally with the state carried verbatim;
* `Break` and `Continue` return their respective results with the state carried
  verbatim;
* `Tick` at clock zero is a timeout with cleared locals;
* `Tick` above clock zero decrements the clock and preserves the locals.

The If checks below pair with `scripts/hol-probes/pan_sem_ite_e2e_probe.out`.
They evaluate the condition from the complete source state before invoking
the selected total branch callback. The oracle includes a condition that
successfully evaluates to `RStruct []` as well as an unbound local and a failed
load; each produces `SOME Error` without changing the state.

The recursive sequence-fragment checks below pair with
`scripts/hol-probes/pan_sem_seq_e2e_probe.out` (`panSemScript.sml:615-618`):
two `Skip`s, first-command `Break`/`Continue`, and `Tick` followed by `Skip`.
The fragment evaluator is structural on those source syntax forms and returns
HOL's result option with the complete source state.

Its restricted recursive `If` checks also pair with
`scripts/hol-probes/pan_sem_ite_e2e_probe.out` (`panSemScript.sml:618-620`):
Const and direct Local conditions select Tick/Skip branches, while missing or
non-word locals produce Error without changing the state.

The RV64 expression-`If` fragment also checks `Op Add` and zero-valued `Op Sub`
conditions, plus failed-load and non-word errors, against the same direct HOL
oracle. The measure-driven fragment now also covers exact `Assign`, `Return`,
and `Raise` cases against `pan_sem_total_fragment_stmt_probe.out`: bounded
Return/Raise clear locals; oversized Return, missing or mismatched exception
shape, and expression failures return Error without changing the state. The
recursive `Dec` cases use direct `dec_restores_locals` and `dec_shape_mismatch`
rows in `pan_sem_e2e_probe.out`: the result is preserved and the shadowed local
is restored after Return clears locals, while a shape mismatch returns Error
with the input state. These constructors remain an explicit fragment, not the
full HOL `evaluate_def` port.
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
    exceptionShapes := fun name => if name == "E" then some .one else none
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

/-- These check the total clauses directly. Their result is a `(result,state)`
    pair, with no evaluator `Option` or fuel layer. -/
def totalSkipClauseGuard : Bool :=
  match panSemEvaluateClockLeaf .skip (totalState 5) with
  | (none, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalBreakClauseGuard : Bool :=
  match panSemEvaluateClockLeaf .break (totalState 5) with
  | (some .break, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalContinueClauseGuard : Bool :=
  match panSemEvaluateClockLeaf .continue (totalState 5) with
  | (some .continue, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalTickClauseGuard : Bool :=
  match panSemEvaluateClockLeaf .tick (totalState 5) with
  | (none, state) => state.clock == 4 && isWordOption 7 (state.locals "x")
  | _ => false

def totalTickZeroClauseGuard : Bool :=
  match panSemEvaluateClockLeaf .tick (totalState 0) with
  | (some .timeOut, state) => state.clock == 0 && (state.locals "x").isNone
  | _ => false

def totalIfThenBranch (state : PanSemState Word64 (FfiState Unit)) :
    Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  (some (.returned (.word (BitVec.ofNat 64 13))), state)

def totalIfElseBranch (state : PanSemState Word64 (FfiState Unit)) :
    Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  (some (.returned (.word (BitVec.ofNat 64 99))), state)

def totalIfState : PanSemState Word64 (FfiState Unit) :=
  { totalState 5 with
    locals := updatePanValueMap (totalState 5).locals "x" (.word (BitVec.ofNat 64 3)) }

def totalIfNonwordState : PanSemState Word64 (FfiState Unit) :=
  { totalIfState with
    locals := updatePanValueMap totalIfState.locals "nonword" (.rStruct []) }

def totalIfEvaluateProgram (program : Prog Word64)
    (state : PanSemState Word64 (FfiState Unit)) :
    Option (PanSemHOLResult Word64) × PanSemState Word64 (FfiState Unit) :=
  match program with
  | .skip => (none, state)
  | .assign .local "x" (.const value) =>
      (none, { state with locals := updatePanValueMap state.locals "x" (.word value) })
  | _ => (some .error, state)

def totalIfNonzeroGuard : Bool :=
  match panSemTotalIfStep (totalState 5) (some (.word (BitVec.ofNat 64 1)))
      totalIfThenBranch totalIfElseBranch with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 13 && state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalIfZeroGuard : Bool :=
  match panSemTotalIfStep (totalState 5) (some (.word (BitVec.ofNat 64 0)))
      totalIfThenBranch totalIfElseBranch with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 99 && state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalIfMissingGuard : Bool :=
  match panSemTotalIfStep (totalState 5) none totalIfThenBranch totalIfElseBranch with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalIfExpressionNonzeroGuard : Bool :=
  match panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfState
      (.const (BitVec.ofNat 64 1))
      (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip with
  | (none, state) =>
      state.clock == 5 && isWordOption 9 (state.locals "x")
  | _ => false

def totalIfExpressionZeroGuard : Bool :=
  match panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfState
      (.const (BitVec.ofNat 64 0))
      (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip with
  | (none, state) =>
      state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfExpressionNonwordGuard : Bool :=
  match panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfState
      (.var .local "missing")
      (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip with
  | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

/-- Unlike an unbound local, this condition evaluates successfully to a
    structured value; HOL still rejects it because `If` requires a word. -/
def totalIfExpressionNonwordValueGuard : Bool :=
  match panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfNonwordState
      (.var .local "nonword")
      (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip with
  | (some .error, state) =>
      state.clock == 5 && isWordOption 3 (state.locals "x") &&
        (match state.locals "nonword" with
         | some (.rStruct []) => true
         | _ => false)
  | _ => false

def totalIfExpressionLoadFailureGuard : Bool :=
  match panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfState
      (.load .one (.const (BitVec.ofNat 64 0)))
      (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip with
  | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
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

def totalSeqFragmentState : PanSemState Word64 (FfiState Unit) :=
  { totalState 5 with
    locals := updatePanValueMap (totalState 5).locals "x" (.word (BitVec.ofNat 64 3)) }

def totalSeqFragmentNormal : PanSemSeqFragment Word64 :=
  .seq (.leaf .skip) (.leaf .skip)

def totalSeqFragmentBreak : PanSemSeqFragment Word64 :=
  .seq (.leaf .break) (.leaf .skip)

def totalSeqFragmentContinue : PanSemSeqFragment Word64 :=
  .seq (.leaf .continue) (.leaf .skip)

def totalSeqFragmentTick : PanSemSeqFragment Word64 :=
  .seq (.leaf .tick) (.leaf .skip)

def totalSeqFragmentGuard : Bool :=
  (match panSemEvaluateSeqFragment totalSeqFragmentNormal totalSeqFragmentState with
   | (none, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateSeqFragment totalSeqFragmentBreak totalSeqFragmentState with
   | (some .break, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateSeqFragment totalSeqFragmentContinue totalSeqFragmentState with
   | (some .continue, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateSeqFragment totalSeqFragmentTick totalSeqFragmentState with
   | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
   | _ => false)

def totalSeqFragmentZeroState : PanSemState Word64 (FfiState Unit) :=
  { totalSeqFragmentState with
    locals := updatePanValueMap totalSeqFragmentState.locals "x" (.word 0) }

def totalSeqFragmentNonwordState : PanSemState Word64 (FfiState Unit) :=
  { totalSeqFragmentState with
    locals := updatePanValueMap totalSeqFragmentState.locals "y" (.rStruct []) }

def totalIfFragmentTrueGuard : Bool :=
  match panSemEvaluateSeqFragment
      (.iteConst (BitVec.ofNat 64 1) (.leaf .tick) (.leaf .skip))
      totalSeqFragmentState with
  | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfFragmentFalseGuard : Bool :=
  match panSemEvaluateSeqFragment
      (.iteConst (BitVec.ofNat 64 0) (.leaf .tick) (.leaf .skip))
      totalSeqFragmentState with
  | (none, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfFragmentLocalTrueGuard : Bool :=
  match panSemEvaluateSeqFragment (.iteLocal "x" (.leaf .tick) (.leaf .skip))
      totalSeqFragmentState with
  | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfFragmentLocalZeroGuard : Bool :=
  match panSemEvaluateSeqFragment (.iteLocal "x" (.leaf .tick) (.leaf .skip))
      totalSeqFragmentZeroState with
  | (none, state) => state.clock == 5 && isWordOption 0 (state.locals "x")
  | _ => false

def totalIfFragmentMissingGuard : Bool :=
  match panSemEvaluateSeqFragment (.iteLocal "missing" (.leaf .tick) (.leaf .skip))
      totalSeqFragmentState with
  | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfFragmentNonwordGuard : Bool :=
  match panSemEvaluateSeqFragment (.iteLocal "y" (.leaf .tick) (.leaf .skip))
      totalSeqFragmentNonwordState with
  | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

def totalIfFragmentGuard : Bool :=
  totalIfFragmentTrueGuard && totalIfFragmentFalseGuard &&
    totalIfFragmentLocalTrueGuard && totalIfFragmentLocalZeroGuard &&
    totalIfFragmentMissingGuard && totalIfFragmentNonwordGuard

def totalExprIfAddTrue : PanSemExprIfFragmentRiscV64 :=
  .ite (.op .add [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2)])
    (.leaf .tick) (.leaf .skip)

def totalExprIfSubZero : PanSemExprIfFragmentRiscV64 :=
  .ite (.op .sub [.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 3)])
    (.leaf .tick) (.leaf .skip)

def totalExprIfFailedLoad : PanSemExprIfFragmentRiscV64 :=
  .ite (.load .one (.const (BitVec.ofNat 64 0))) (.leaf .tick) (.leaf .skip)

def totalExprIfNonwordLocal : PanSemExprIfFragmentRiscV64 :=
  .ite (.var .local "y") (.leaf .tick) (.leaf .skip)

def totalExprIfThenSeq : PanSemExprIfFragmentRiscV64 :=
  .seq totalExprIfAddTrue (.leaf .skip)

def totalDecRestoresLocals : PanSemExprIfFragmentRiscV64 :=
  .dec "x" .one (.const (BitVec.ofNat 64 9))
    (.returnValue (.var .local "x"))

def totalDecShapeMismatch : PanSemExprIfFragmentRiscV64 :=
  .dec "x" .one (.rStruct []) (.leaf .skip)

def totalExprIfFragmentGuard : Bool :=
  (match panSemEvaluateExprIfFragmentRiscV64 totalExprIfAddTrue totalSeqFragmentState with
   | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64 totalExprIfSubZero totalSeqFragmentState with
   | (none, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64 totalExprIfFailedLoad totalSeqFragmentState with
   | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64 totalExprIfNonwordLocal
      totalSeqFragmentNonwordState with
   | (some .error, state) =>
       state.clock == 5 && isWordOption 3 (state.locals "x") &&
         (match state.locals "y" with | some (.rStruct []) => true | _ => false)
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64 totalDecRestoresLocals
      (totalState 5) with
   | (some (.returned (.word value)), state) =>
       value == BitVec.ofNat 64 9 && state.clock == 5 &&
         isWordOption 7 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64 totalDecShapeMismatch
      (totalState 5) with
   | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
   | _ => false)

/-- The measure-driven implementation is checked against the same direct HOL
    expression-If oracle rows as the structurally recursive support fragment. -/
def totalExprIfFragmentMeasureGuard : Bool :=
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalExprIfAddTrue totalSeqFragmentState with
   | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalExprIfSubZero totalSeqFragmentState with
   | (none, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalExprIfFailedLoad totalSeqFragmentState with
   | (some .error, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalExprIfNonwordLocal totalSeqFragmentNonwordState with
   | (some .error, state) =>
       state.clock == 5 && isWordOption 3 (state.locals "x") &&
         (match state.locals "y" with | some (.rStruct []) => true | _ => false)
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalExprIfThenSeq totalSeqFragmentState with
   | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalDecRestoresLocals (totalState 5) with
   | (some (.returned (.word value)), state) =>
       value == BitVec.ofNat 64 9 && state.clock == 5 &&
         isWordOption 7 (state.locals "x")
   | _ => false) &&
  (match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      totalDecShapeMismatch (totalState 5) with
   | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
   | _ => false)

/-- A state whose global `g` is bound, for the global-assignment case. -/
def totalAssignState : PanSemState Word64 (FfiState Unit) :=
  { totalState 5 with
    globals := fun name =>
      if name == "g" then some (.word (BitVec.ofNat 64 4)) else none }

/-- The Assign step consumes an already evaluated source result (HOL's
    `eval s src`).  These guards exercise the post-evaluation composition;
    faithful source evaluation is a separate obligation. -/
def assignLocalGuard : Bool :=
  match panSemTotalAssignStep (totalState 5) .local "x" (some (.word (BitVec.ofNat 64 9))) with
  | (.normal, state) => state.clock == 5 && isWordOption 9 (state.locals "x")
  | _ => false

def assignGlobalGuard : Bool :=
  match panSemTotalAssignStep totalAssignState .global "g" (some (.word (BitVec.ofNat 64 9))) with
  | (.normal, state) => state.clock == 5 && isWordOption 9 (state.globals "g")
  | _ => false

def assignFreshGuard : Bool :=
  match panSemTotalAssignStep (totalState 5) .local "y" (some (.word (BitVec.ofNat 64 9))) with
  | (.error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def assignMissingGuard : Bool :=
  match panSemTotalAssignStep (totalState 5) .local "x" none with
  | (.error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalReturnGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.returnValue (.const (BitVec.ofNat 64 7))) (totalState 5) with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 5 &&
        (state.locals "x").isNone && (state.globals "g").isNone
  | _ => false

def totalReturnMissingGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.returnValue (.var .local "missing")) (totalState 5) with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalReturnOversizeGuard : Bool :=
  let tooManyWords : Exp Word64 :=
    .rStruct (List.replicate 33 (.const (BitVec.ofNat 64 1)))
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.returnValue tooManyWords) (totalState 5) with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalRaiseGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.raiseException "E" (.const (BitVec.ofNat 64 4))) (totalState 5) with
  | (some (.exception "E" (.word value)), state) =>
      value == BitVec.ofNat 64 4 && state.clock == 5 && (state.locals "x").isNone
  | _ => false

def totalRaiseShapeMismatchGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.raiseException "E" (.rStruct [])) (totalState 5) with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalRaiseMissingShapeGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.raiseException "Missing" (.const (BitVec.ofNat 64 4))) (totalState 5) with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalRaiseMissingValueGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.raiseException "E" (.var .local "missing")) (totalState 5) with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalRaiseOversizeGuard : Bool :=
  let tooManyWords : Exp Word64 :=
    .rStruct (List.replicate 33 (.const (BitVec.ofNat 64 1)))
  let oversizedState :=
    { totalState 5 with
      exceptionShapes := fun name =>
        if name == "E" then some (.comb (List.replicate 33 .one)) else none }
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.raiseException "E" tooManyWords) oversizedState with
  | (some .error, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalIfAssignTrueGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.ite (.const (BitVec.ofNat 64 1))
        (.assign .local "x" (.const (BitVec.ofNat 64 9))) (.leaf .skip))
      (totalState 5) with
  | (none, state) => state.clock == 5 && isWordOption 9 (state.locals "x")
  | _ => false

def totalIfAssignFalseGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.ite (.const (BitVec.ofNat 64 0))
        (.assign .local "x" (.const (BitVec.ofNat 64 9))) (.leaf .skip))
      (totalState 5) with
  | (none, state) => state.clock == 5 && isWordOption 7 (state.locals "x")
  | _ => false

def totalSeqAssignReturnGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.seq (.assign .local "x" (.const (BitVec.ofNat 64 9)))
        (.returnValue (.const (BitVec.ofNat 64 7)))) (totalState 5) with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 5 && (state.locals "x").isNone
  | _ => false

def totalSeqRaiseStopGuard : Bool :=
  match panSemEvaluateExprIfFragmentRiscV64ByMeasure
      (.seq (.raiseException "E" (.const (BitVec.ofNat 64 4)))
        (.assign .local "x" (.const (BitVec.ofNat 64 9)))) (totalState 5) with
  | (some (.exception "E" (.word value)), state) =>
      value == BitVec.ofNat 64 4 && state.clock == 5 && (state.locals "x").isNone
  | _ => false

def totalGuard : Bool :=
  skipGuard && tickSuccGuard && tickZeroGuard && totalSkipClauseGuard &&
    totalBreakClauseGuard && totalContinueClauseGuard && totalTickClauseGuard &&
    totalTickZeroClauseGuard && seqNormalGuard && seqBreakGuard &&
    seqContinueGuard && seqTickGuard && totalSeqFragmentGuard && totalIfFragmentGuard &&
    totalExprIfFragmentGuard && totalExprIfFragmentMeasureGuard &&
    totalIfNonzeroGuard && totalIfZeroGuard &&
    totalIfMissingGuard && totalIfExpressionNonzeroGuard && totalIfExpressionZeroGuard &&
    totalIfExpressionNonwordGuard && totalIfExpressionNonwordValueGuard &&
    totalIfExpressionLoadFailureGuard &&
    assignLocalGuard && assignGlobalGuard &&
    assignFreshGuard && assignMissingGuard && totalReturnGuard &&
    totalReturnMissingGuard && totalReturnOversizeGuard && totalRaiseGuard &&
    totalRaiseShapeMismatchGuard && totalRaiseMissingShapeGuard &&
    totalRaiseMissingValueGuard && totalRaiseOversizeGuard &&
    totalIfAssignTrueGuard && totalIfAssignFalseGuard &&
    totalSeqAssignReturnGuard && totalSeqRaiseStopGuard

#guard totalGuard

example :
    panSemTotalIfStep (totalState 5) (some (.word (BitVec.ofNat 64 1)))
        totalIfThenBranch totalIfElseBranch = totalIfThenBranch (totalState 5) := by
  apply panSemTotalIfStep_nonzero
  decide

example :
    panSemTotalIfStep (totalState 5) (some (.word (BitVec.ofNat 64 0)))
        totalIfThenBranch totalIfElseBranch = totalIfElseBranch (totalState 5) := by
  apply panSemTotalIfStep_zero

example :
    panSemTotalIfStep (totalState 5) none totalIfThenBranch totalIfElseBranch =
        (some .error, totalState 5) := by
  rfl

example :
    panSemEvaluateIfClauseRiscV64 totalIfEvaluateProgram totalIfNonwordState
        (.var .local "nonword")
        (.assign .local "x" (.const (BitVec.ofNat 64 9))) .skip =
      (some .error, totalIfNonwordState) := by
  apply panSemEvaluateIfClauseRiscV64_eval_nonword
  change (evalPanValueExp totalIfNonwordState.structs totalIfNonwordState.locals
      totalIfNonwordState.globals totalIfNonwordState.memory
      totalIfNonwordState.baseAddress totalIfNonwordState.topAddress
      panSemBitVec64BytesInWord (.var .local "nonword")
      (memoryAccess := some (panSemBitVec64MemoryAccess totalIfNonwordState))) =
    some (.rStruct [])
  simp [totalIfNonwordState, totalIfState, totalState, updatePanValueMap,
    evalPanValueExp]

example :
    panSemEvaluateClockLeaf .skip (totalState 5) =
      (none, totalState 5) := by
  rfl

example :
    panSemEvaluateClockLeaf .break (totalState 5) =
      (some .break, totalState 5) := by
  rfl

example :
    panSemEvaluateClockLeaf .continue (totalState 5) =
      (some .continue, totalState 5) := by
  rfl

example :
    panSemEvaluateClockLeaf .tick (totalState 0) =
      (some .timeOut, { totalState 0 with locals := fun _ => none }) := by
  simp [panSemEvaluateClockLeaf, totalState]

example :
    panSemEvaluateClockLeaf .tick (totalState 5) =
      (none, { totalState 5 with clock := 4 }) := by
  simp [panSemEvaluateClockLeaf, totalState]

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
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.break : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateBreak (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_break_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

example :
    (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) (totalState 5) (.continue : Prog Word64)).map
        panSemTotalOfExecuted = some (panSemEvaluateContinue (totalState 5)) :=
  panSemEvaluateCodeStateWithPostState_continue_total statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (totalState 5)

example :
    panSemTotalAssignStep (totalState 5) .local "x" (some (.word (BitVec.ofNat 64 9))) =
      (.normal,
        { totalState 5 with
          locals := updatePanValueMap (totalState 5).locals "x" (.word (BitVec.ofNat 64 9)) }) :=
  panSemTotalAssignStep_normal_local (totalState 5) "x" (.word (BitVec.ofNat 64 9))
    (by simp [panValueAssignmentValid, panValueShape, panShapeMatches, totalState])

example :
    panSemTotalAssignStep (totalState 5) .local "x" none =
      (.error, totalState 5) :=
  panSemTotalAssignStep_none (totalState 5) .local "x"

def runChecks : IO Bool := do
  if totalSkipClauseGuard then
    IO.println "PASS total panSem Skip clause returns NONE and the same source state"
  else IO.println "FAIL total panSem Skip clause returns NONE and the same source state"
  if totalBreakClauseGuard then
    IO.println "PASS total panSem Break clause returns SOME Break and the same source state"
  else IO.println "FAIL total panSem Break clause returns SOME Break and the same source state"
  if totalContinueClauseGuard then
    IO.println "PASS total panSem Continue clause returns SOME Continue and the same source state"
  else IO.println "FAIL total panSem Continue clause returns SOME Continue and the same source state"
  if totalTickClauseGuard && totalTickZeroClauseGuard then
    IO.println "PASS total panSem Tick clauses match the clock branches"
  else IO.println "FAIL total panSem Tick clauses match the clock branches"
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
  if totalReturnGuard then
    IO.println "PASS panSem total Return accepts bounded value and clears locals"
  else IO.println "FAIL panSem total Return accepts bounded value and clears locals"
  if totalReturnMissingGuard && totalReturnOversizeGuard then
    IO.println "PASS panSem total Return rejects missing and oversized values without state change"
  else IO.println "FAIL panSem total Return rejects missing and oversized values without state change"
  if totalRaiseGuard then
    IO.println "PASS panSem total Raise checks exception shape and clears locals"
  else IO.println "FAIL panSem total Raise checks exception shape and clears locals"
  if totalRaiseShapeMismatchGuard && totalRaiseMissingShapeGuard &&
      totalRaiseMissingValueGuard && totalRaiseOversizeGuard then
    IO.println "PASS panSem total Raise errors preserve state for shape/size/evaluation failures"
  else IO.println "FAIL panSem total Raise errors preserve state for shape/size/evaluation failures"
  if totalIfAssignTrueGuard && totalIfAssignFalseGuard then
    IO.println "PASS panSem total If selects statement branches against direct HOL cases"
  else IO.println "FAIL panSem total If selects statement branches against direct HOL cases"
  if totalSeqAssignReturnGuard && totalSeqRaiseStopGuard then
    IO.println "PASS panSem total Seq handles Return and Raise control outcomes"
  else IO.println "FAIL panSem total Seq handles Return and Raise control outcomes"
  if totalExprIfFragmentGuard && totalExprIfFragmentMeasureGuard then
    IO.println "PASS panSem total Dec restores shadowed locals and rejects shape mismatch against HOL"
  else IO.println "FAIL panSem total Dec restores shadowed locals and rejects shape mismatch against HOL"
  pure totalGuard

example :
    panSemEvalMeasureRel (totalState 5, Prog.skip)
      (totalState 5, Prog.ite (.const (BitVec.ofNat 64 1)) .skip .tick) :=
  panSemEvalMeasureRel_ite_branch (totalState 5)
    (.const (BitVec.ofNat 64 1)) .skip .tick .skip (Or.inl rfl)

example :
    panSemEvalMeasureRel (totalState 5, Prog.skip)
      (totalState 5,
        Prog.dec "x" .one (.const (BitVec.ofNat 64 9)) .skip) :=
  panSemEvalMeasureRel_decBody (totalState 5) "x" .one
    (.const (BitVec.ofNat 64 9)) .skip

example :
    panSemEvalMeasureRel
      (totalState 4, Prog.while (.const (BitVec.ofNat 64 1)) (.skip : Prog Word64))
      (totalState 5, Prog.skip) :=
  panSemEvalMeasureRel_of_clock_lt (by decide)

example :
    panSemEvalMeasureRel
      ({totalState 5 with clock := decPanClock 5},
        (Prog.seq .skip (.while (.const (BitVec.ofNat 64 1)) .tick) : Prog Word64))
      (totalState 5, Prog.call none "callee" []) := by
  apply panSemEvalMeasureRel_of_clock_le_decPanClock (currentState := totalState 5)
    (nextProgram := Prog.seq .skip (.while (.const (BitVec.ofNat 64 1)) .tick))
    (currentProgram := Prog.call none "callee" [])
  · decide
  · decide

example :
    panSemEvalMeasureRel
      ({totalState 5 with clock := decPanClock 5}, Prog.seq .skip .tick)
      (totalState 5,
        Prog.decCall "x" .one "callee" [] (Prog.seq .skip .tick)) := by
  apply panSemEvalMeasureRel_decCallBody ({totalState 5 with clock := decPanClock 5})
    (totalState 5) "x" .one "callee" [] (Prog.seq .skip .tick)
  decide

example :
    panSemEvalMeasureRel (totalState 4, Prog.tick)
      (totalState 5, Prog.seq .skip .tick) :=
  panSemEvalMeasureRel_seq_branch (totalState 4) (totalState 5)
    .skip .tick .tick (by decide) (Or.inr rfl)

example :
    panSemEvalMeasureRel
      (panSemFixClock 5 (totalState 7), Prog.tick)
      (totalState 5, Prog.seq .skip .tick) := by
  apply panSemEvalMeasureRel_seq_branch (panSemFixClock 5 (totalState 7))
    (totalState 5) .skip .tick .tick
  · exact panSemFixClock_clock_le 5 (totalState 7)
  · exact Or.inr rfl

end Flapjack.Test.PanSemTotalParity
