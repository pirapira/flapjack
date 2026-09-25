import Flapjack.Pancake.Semantics.PanSem.ControlExact
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-! # Parity for the exact HOL panSem control-flow clause steps

Replays the direct original-HOL rows in
`scripts/hol-probes/pan_sem_e2e_probe.out` for `Seq`/`If`/`While`/`Break`/
`Continue`/`Annot` (rows `seq_two_assigns`, `seq_first_errors`, `if_true`,
`if_false`, `if_error`, `while_cond_zero`, `while_timeout`, `while_break`,
`while_continue_then_zero`, `while_error_condition`, `break_clause`,
`continue_clause`, `annot_clause`) against the untagged exact clause steps in
`Flapjack/Pancake/Semantics/PanSem/ControlExact.lean`.
-/

namespace Flapjack.Test.PanSemControlExactParity

open Flapjack
open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL)

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private abbrev Word8 := RiscV.Word 8

abbrev baseState (clock : Nat) : PanSemStateExact 8 Unit :=
  { locals := fun name =>
      if name = ml "x" then some (.val (.word (0 : Word8)))
      else if name = ml "c" then some (.val (.word (1 : Word8)))
      else none
    globals := fun _ => none
    structs := []
    code := fun _ => none
    eshapes := fun _ => none
    memory := fun _ => .word (0 : Word8)
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := clock
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := (0 : Word8)
    topAddr := (100 : Word8) }

abbrev state5 : PanSemStateExact 8 Unit := baseState 5
abbrev stateFalse : PanSemStateExact 8 Unit :=
  { baseState 5 with
    locals := fun name =>
      if name = ml "c" then some (.val (.word (0 : Word8)))
      else if name = ml "x" then some (.val (.word (0 : Word8)))
      else none }
abbrev stateNoX : PanSemStateExact 8 Unit :=
  { baseState 5 with locals := fun _ => none }
abbrev stateClock0 : PanSemStateExact 8 Unit :=
  { baseState 0 with
    locals := fun name => if name = ml "x" then some (.val (.word (0 : Word8))) else none }
abbrev stateX1 : PanSemStateExact 8 Unit :=
  { baseState 5 with
    locals := fun name => if name = ml "x" then some (.val (.word (1 : Word8))) else none }

/-- Expression evaluator fixture: constants and local variables only. -/
def evalExpressionFixture (state : PanSemStateExact 8 Unit) : ExpHOL 8 → Option (ValueHOL 8)
  | .const value => some (.val (.word value))
  | .var .local name => state.locals name
  | _ => none

/-- Program evaluator stub used by the parity guards: `skip`, `break`,
`continue` and constant local assignment. -/
def evaluateStub :
    ProgHOL 8 → PanSemStateExact 8 Unit →
      Option (PanSemResultExact 8) × PanSemStateExact 8 Unit
  | .skip, state => (none, state)
  | .break, state => (some .break, state)
  | .continue, state => (some .continue, state)
  | .assign _ name (.const value), state =>
      (none, { state with
        locals := fun current =>
          if current = name then some (.val (.word value)) else state.locals current })
  | _, state => (some .error, state)

/-- Stub for the recursive `While` continuation: in the `while_continue_then_zero`
row the condition is false after the body, so normal completion is returned. -/
def recurseStub (state : PanSemStateExact 8 Unit) :
    Option (PanSemResultExact 8) × PanSemStateExact 8 Unit :=
  (none, state)

def resultTag {width : Nat} [NeZero width] (result : Option (PanSemResultExact width)) : Nat :=
  match result with
  | none => 0
  | some .error => 1
  | some .timeOut => 2
  | some .break => 3
  | some .continue => 4
  | some (.returned _) => 5
  | some (.exception _ _) => 6
  | some (.finalFfi _) => 7

def isNoneResult {width : Nat} [NeZero width]
    (result : Option (PanSemResultExact width)) : Bool :=
  match result with
  | none => true
  | _ => false

def isErrorResult {width : Nat} [NeZero width]
    (result : Option (PanSemResultExact width)) : Bool :=
  match result with
  | some .error => true
  | _ => false

def isTimeOutResult {width : Nat} [NeZero width]
    (result : Option (PanSemResultExact width)) : Bool :=
  match result with
  | some .timeOut => true
  | _ => false

def localsWordOf (state : PanSemStateExact 8 Unit) (name : MlS) : Option Nat :=
  match state.locals name with
  | some (.val (.word value)) => some value.toNat
  | _ => none

/-- `seq_two_assigns = (NONE, SOME (ValWord 2w), 5)`. -/
def seqTwoAssignsGuard : Bool :=
  let result := seqStepHOLExact state5
    (.assign .local (ml "x") (.const 1)) (.assign .local (ml "x") (.const 2)) evaluateStub
  isNoneResult result.1 && localsWordOf result.2 (ml "x") == some 2 && result.2.clock == 5

/-- `seq_first_errors = (SOME Error, SOME (ValWord 0w))`. -/
def seqFirstErrorsGuard : Bool :=
  let result := seqStepHOLExact state5
    (.assign .local (ml "x") (.var .local (ml "missing")))
    (.assign .local (ml "x") (.const 2)) evaluateStub
  isErrorResult result.1 && localsWordOf result.2 (ml "x") == some 0

/-- `if_true = (NONE, SOME (ValWord 1w))`. -/
def ifTrueGuard : Bool :=
  let result := ifStepHOLExact state5 (.var .local (ml "c"))
    (.assign .local (ml "x") (.const 1)) (.assign .local (ml "x") (.const 2))
    evalExpressionFixture evaluateStub
  isNoneResult result.1 && localsWordOf result.2 (ml "x") == some 1

/-- `if_false = (NONE, SOME (ValWord 2w))` (false is zero). -/
def ifFalseGuard : Bool :=
  let result := ifStepHOLExact stateFalse (.var .local (ml "c"))
    (.assign .local (ml "x") (.const 1)) (.assign .local (ml "x") (.const 2))
    evalExpressionFixture evaluateStub
  isNoneResult result.1 && localsWordOf result.2 (ml "x") == some 2

/-- `if_error = SOME Error`. -/
def ifErrorGuard : Bool :=
  let result := ifStepHOLExact stateNoX (.var .local (ml "missing"))
    .skip .skip evalExpressionFixture evaluateStub
  isErrorResult result.1

/-- `while_cond_zero = (NONE, 5)`. -/
def whileCondZeroGuard : Bool :=
  let result := whileStepHOLExact stateNoX (.const 0) .skip
    evalExpressionFixture evaluateStub recurseStub
  isNoneResult result.1 && result.2.clock == 5

/-- `while_timeout = (SOME TimeOut, NONE)` (locals cleared). -/
def whileTimeoutGuard : Bool :=
  let result := whileStepHOLExact stateClock0 (.const 1) .skip
    evalExpressionFixture evaluateStub recurseStub
  isTimeOutResult result.1 && result.2.clock == 0 && (localsWordOf result.2 (ml "x")).isNone

/-- `while_break = (NONE, 4, SOME (ValWord 1w))`. -/
def whileBreakGuard : Bool :=
  let result := whileStepHOLExact stateX1 (.var .local (ml "x")) .break
    evalExpressionFixture evaluateStub recurseStub
  isNoneResult result.1 && result.2.clock == 4 && localsWordOf result.2 (ml "x") == some 1

/-- `while_continue_then_zero = (NONE, 4, SOME (ValWord 0w))`. -/
def whileContinueThenZeroGuard : Bool :=
  let result := whileStepHOLExact stateX1 (.var .local (ml "x"))
    (.assign .local (ml "x") (.const 0)) evalExpressionFixture evaluateStub recurseStub
  isNoneResult result.1 && result.2.clock == 4 && localsWordOf result.2 (ml "x") == some 0

/-- `while_error_condition = SOME Error`. -/
def whileErrorGuard : Bool :=
  let result := whileStepHOLExact stateNoX (.var .local (ml "missing")) .skip
    evalExpressionFixture evaluateStub recurseStub
  isErrorResult result.1

/-- `break_clause = (SOME Break, 5)`. -/
def breakGuard : Bool :=
  let result := breakStepHOLExact state5
  resultTag result.1 == 3 && result.2.clock == 5

/-- `continue_clause = (SOME Continue, 5)`. -/
def continueGuard : Bool :=
  let result := continueStepHOLExact state5
  resultTag result.1 == 4 && result.2.clock == 5

/-- `annot_clause = (NONE, 5)`. -/
def annotGuard : Bool :=
  let result := annotStepHOLExact state5 (ml "t") (ml "u")
  isNoneResult result.1 && result.2.clock == 5

def controlExactGuard : Bool :=
  seqTwoAssignsGuard && seqFirstErrorsGuard && ifTrueGuard && ifFalseGuard && ifErrorGuard &&
    whileCondZeroGuard && whileTimeoutGuard && whileBreakGuard && whileContinueThenZeroGuard &&
    whileErrorGuard && breakGuard && continueGuard && annotGuard

#eval seqTwoAssignsGuard
#eval ifTrueGuard
#eval whileBreakGuard
#eval whileContinueThenZeroGuard
#eval breakGuard
#guard controlExactGuard

def runChecks : IO Bool := do
  if controlExactGuard then
    IO.println "PASS exact panSem Seq/If/While/Break/Continue/Annot clause steps (13 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem Seq/If/While/Break/Continue/Annot clause steps"
    pure false

end Flapjack.Test.PanSemControlExactParity
