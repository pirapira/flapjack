import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.TotalMeasure
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# HOL-shaped result interface for a total Pancake `evaluate`

`cakeml/pancake/semantics/panSemScript.sml:68-75` declares

```
result = Error | TimeOut | Break | Continue
       | Return ('a v) | Exception mlstring ('a v) | FinalFFI final_event
```

and `evaluate : prog # state -> result option # state` (lines 556-736) returns
the result paired with the final state, with HOL's `NONE` for a normal
completion.

The executed production evaluator `panSemEvaluateCodeStateWithPostState`
returns an `Option` of a structured control result whose outcome embeds the
state components, so its statements cannot carry an exact HOL `evaluate` tag.
This module starts the genuinely HOL-shaped total interface:

* `PanSemProgResult` is an existing helper carrier whose `normal` constructor
  represents HOL `NONE`; its return payload is list-shaped, so it is not an
  exact encoding of HOL `result option`;
* `PanSemHOLResult` mirrors the constructors and payloads of HOL `result`;
* `panSemProgResultOfClockResult` maps the executed clocked result onto it;
* `panSemEvaluateClockLeaf` is a total evaluator on exactly the four
  nonrecursive constructors `Skip`, `Break`, `Continue`, and `Tick`. Its state
  is the complete production `PanSemState`; there is no evaluator `Option` or
  fuel layer. The remaining constructors are outside this restricted domain,
  so this is not the whole-program `panSemEvaluate`;
* `panSemTotalSeqStep` is the HOL `Seq` composition (clamp the first result's
  clock with `fix_clock`, continue only on a normal completion) as a helper over
  an already evaluated first pair and a continuation, not a whole-program
  evaluator.

The state half is the production `PanSemState`, so the eventual total
`panSemEvaluate` returns a `PanSemProgResult α σ × PanSemState α (FfiState σ)`
pair with no `Option`/fuel wrapper, using the source recursion measure
`panSemEvalMeasure`, whose coordinates are `(state.clock, panSemProgFuel
program)`.  `panSemTotalOfExecuted` is only a proved
relation between the executed evaluator and this interface; it never defines
total evaluation.  Everything here is untagged until that total evaluator and
its exact HOL statement are established.
-/

namespace Flapjack

/-- Existing helper encoding of the outcomes projected from the executed
    clocked evaluator. `.normal` represents HOL `NONE`; this is not an exact
    HOL result carrier because `.returned` holds a list, while HOL `Return`
    carries one value. -/
inductive PanSemProgResult (α : Type u) (σ : Type v) where
  | normal
  | error
  | timeout
  | broke
  | continued
  | returned (values : List (PanValue α))
  | raised (exception : ExceptionId) (value : PanValue α)
  | finalFfi (event : FfiFinalEvent)

/-- Project the executed clocked result onto the HOL-shaped `result`. -/
def panSemProgResultOfClockResult (result : PanValueFfiClockResult α σ) :
    PanSemProgResult α σ :=
  match result.1 with
  | .control (.normal _ _ _ _) => .normal
  | .control (.error _ _ _ _) => .error
  | .control (.broke _ _ _ _) => .broke
  | .control (.continued _ _ _ _) => .continued
  | .control (.returned _ _ _ _ values) => .returned values
  | .control (.raised _ _ _ _ exception value) => .raised exception value
  | .control (.finalFfi _ _ _ _ event) => .finalFfi event
  | .timeout _ _ _ _ => .timeout

@[simp] theorem panSemProgResultOfClockResult_normal
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.normal locals globals memory ffi), clock) :
          PanValueFfiClockResult α σ) = .normal := rfl

@[simp] theorem panSemProgResultOfClockResult_error
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.error locals globals memory ffi), clock) :
          PanValueFfiClockResult α σ) = .error := rfl

@[simp] theorem panSemProgResultOfClockResult_timeout
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.timeout locals globals memory ffi, clock) :
          PanValueFfiClockResult α σ) = .timeout := rfl

@[simp] theorem panSemProgResultOfClockResult_broke
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.broke locals globals memory ffi), clock) :
          PanValueFfiClockResult α σ) = .broke := rfl

@[simp] theorem panSemProgResultOfClockResult_continued
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.continued locals globals memory ffi), clock) :
          PanValueFfiClockResult α σ) = .continued := rfl

@[simp] theorem panSemProgResultOfClockResult_returned
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (values : List (PanValue α)) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.returned locals globals memory ffi values), clock) :
          PanValueFfiClockResult α σ) = .returned values := rfl

@[simp] theorem panSemProgResultOfClockResult_raised
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (exception : ExceptionId) (value : PanValue α) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.raised locals globals memory ffi exception value), clock) :
          PanValueFfiClockResult α σ) = .raised exception value := rfl

@[simp] theorem panSemProgResultOfClockResult_finalFfi
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (event : FfiFinalEvent) (clock : Nat) :
    panSemProgResultOfClockResult
        ((.control (.finalFfi locals globals memory ffi event), clock) :
          PanValueFfiClockResult α σ) = .finalFfi event := rfl

/-- Project an executed `(clocked result, state)` pair into the legacy helper
    outcome/state carrier. This is a proved relation about the executed
    evaluator; it is not part of `panSemEvaluateClockLeaf` and is not the exact
    HOL `result option` carrier. -/
def panSemTotalOfExecuted
    (pair : PanValueFfiClockResult α σ × PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  (panSemProgResultOfClockResult pair.1, pair.2)

/-! ## Total evaluator for the clock leaves

    This evaluator is total on its explicitly restricted four-constructor
    domain, preserving the full source state. It is not the recursive evaluator
    for all `Prog` forms. The leaf evaluator below returns `Option
    PanSemHOLResult`, where the option is HOL's result option and is not a
    fuel/partial-evaluation wrapper. -/

/-- Lean counterpart of the constructors and payloads of
    `panSem$result` (`panSemScript.sml:68-75`). Names are made Lean-safe; this
    carrier does not by itself port the whole `evaluate` function. -/
inductive PanSemHOLResult (α : Type u) where
  | error
  | timeOut
  | break
  | continue
  | returned (value : PanValue α)
  | exception (exception : ExceptionId) (value : PanValue α)
  | finalFfi (event : FfiFinalEvent)

/-- Domain of the four nonrecursive `panSem$evaluate` clock leaves. -/
inductive PanSemClockLeaf where
  | skip
  | break
  | continue
  | tick
  deriving DecidableEq, Repr

/-- Embed a clock leaf into the matching production Pancake syntax. -/
def PanSemClockLeaf.toProg {α : Type u} : PanSemClockLeaf → Prog α
  | .skip => .skip
  | .break => .break
  | .continue => .continue
  | .tick => .tick

/-- HOL `Skip` (`cakeml/pancake/semantics/panSemScript.sml:557`):
    normal completion with the state carried verbatim. -/
def panSemEvaluateSkip (state : PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  (.normal, state)

/-- HOL `Break` (`cakeml/pancake/semantics/panSemScript.sml:590`): return the
    break result and carry the faithful source state verbatim. -/
def panSemEvaluateBreak (state : PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  (.broke, state)

/-- HOL `Continue` (`cakeml/pancake/semantics/panSemScript.sml:591`): return the
    continue result and carry the faithful source state verbatim. -/
def panSemEvaluateContinue (state : PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  (.continued, state)

/-- HOL `Tick` (`cakeml/pancake/semantics/panSemScript.sml:653-655`): at clock
    zero a timeout with cleared locals, otherwise normal completion with the
    clock decremented and every other component preserved. -/
def panSemEvaluateTick (state : PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  if state.clock = 0 then
    (.timeout, { state with locals := fun _ => none })
  else
    (.normal, { state with clock := state.clock - 1 })

/-- Total `panSem$evaluate` equations for the restricted clock-leaf domain
    (`panSemScript.sml:557, 623-624, 653-655`). The result/state pair uses HOL's
    `result option` shape over the complete source state. This restricted
    declaration is not the full `Prog` evaluator and is not tagged as HOL's
    `evaluate_def`. -/
def panSemEvaluateClockLeaf (leaf : PanSemClockLeaf)
    (state : PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match leaf with
  | .skip => (none, state)
  | .break => (some .break, state)
  | .continue => (some .continue, state)
  | .tick =>
      if state.clock = 0 then
        (some .timeOut, { state with locals := fun _ => none })
      else
        (none, { state with clock := state.clock - 1 })

@[simp] theorem panSemEvaluateClockLeaf_skip
    (state : PanSemState α (FfiState σ)) :
    panSemEvaluateClockLeaf .skip state = (none, state) := rfl

@[simp] theorem panSemEvaluateClockLeaf_break
    (state : PanSemState α (FfiState σ)) :
    panSemEvaluateClockLeaf .break state = (some .break, state) := rfl

@[simp] theorem panSemEvaluateClockLeaf_continue
    (state : PanSemState α (FfiState σ)) :
    panSemEvaluateClockLeaf .continue state = (some .continue, state) := rfl

theorem panSemEvaluateClockLeaf_tick_zero
    (state : PanSemState α (FfiState σ)) (hclock : state.clock = 0) :
    panSemEvaluateClockLeaf .tick state =
      (some .timeOut, { state with locals := fun _ => none }) := by
  simp [panSemEvaluateClockLeaf, hclock]

theorem panSemEvaluateClockLeaf_tick_positive
    (state : PanSemState α (FfiState σ)) (hclock : state.clock ≠ 0) :
    panSemEvaluateClockLeaf .tick state =
      (none, { state with clock := state.clock - 1 }) := by
  simp [panSemEvaluateClockLeaf, hclock]

/-! ## Compositional `If` step

    HOL `If` evaluates its expression in the entry state, selects the then
    branch for every nonzero word and the else branch for zero, and evaluates
    the selected branch in that same state (`panSemScript.sml:618-621`). This
    helper exposes that composition after the source expression has been
    evaluated and with total branch continuations. The `Option` values here are
    the semantic results of HOL `eval` and `result option`; neither is a Lean
    evaluator-fuel wrapper. -/

/-- HOL `If` composition after its condition evaluation. A missing or
    non-word-valued condition produces `SOME Error` and leaves the complete
    source state unchanged. The selected continuation receives the original
    state. This is useful total support for `If`, not a standalone port of the
    full `evaluate` clause, because expression evaluation is an explicit input. -/
def panSemTotalIfStep [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ))
    (evaluatedCondition : Option (PanValue α))
    (thenBranch elseBranch :
      PanSemState α (FfiState σ) →
        Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match evaluatedCondition with
  | some (.word value) =>
      if value = 0 then elseBranch state else thenBranch state
  | _ => (some .error, state)

theorem panSemTotalIfStep_nonzero [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (value : α) (hzero : value ≠ 0)
    (thenBranch elseBranch :
      PanSemState α (FfiState σ) →
        Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalIfStep state (some (.word value)) thenBranch elseBranch =
      thenBranch state := by
  simp [panSemTotalIfStep, hzero]

theorem panSemTotalIfStep_zero [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ))
    (thenBranch elseBranch :
      PanSemState α (FfiState σ) →
        Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalIfStep state (some (.word 0)) thenBranch elseBranch =
      elseBranch state := by
  simp [panSemTotalIfStep]

theorem panSemTotalIfStep_error [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ))
    (evaluatedCondition : Option (PanValue α))
    (hbad : ∀ value, evaluatedCondition ≠ some (.word value))
    (thenBranch elseBranch :
      PanSemState α (FfiState σ) →
        Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalIfStep state evaluatedCondition thenBranch elseBranch =
      (some .error, state) := by
  cases evaluatedCondition with
  | none => rfl
  | some value =>
      cases value with
      | word word => exact (hbad word rfl).elim
      | rStruct values => rfl
      | nStruct name fields => rfl

/-- RISC-V 64-bit source-state `If` clause. Unlike
    `panSemTotalIfStep`, this definition evaluates the condition expression
    itself with `evalPanSemStateExp`, deriving locals, globals, structs,
    memory domains, endian mode, and address bounds from the complete
    `PanSemState`. The selected branch callback receives that same state and
    returns the total HOL result/state pair. The callback remains an untagged
    recursion boundary until the public whole-program total evaluator exists;
    this is not a port of the complete recursive HOL `evaluate_def`. -/
def panSemEvaluateIfClauseRiscV64 [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (evaluateProgram : Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (condition : Exp (RiscV.Word 64))
    (thenBranch elseBranch : Prog (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalIfStep state (evalPanSemStateExp state condition)
    (evaluateProgram thenBranch) (evaluateProgram elseBranch)

theorem panSemEvaluateIfClauseRiscV64_word
    (evaluateProgram : Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (condition : Exp (RiscV.Word 64))
    (thenBranch elseBranch : Prog (RiscV.Word 64))
    (value : RiscV.Word 64)
    (heval : evalPanSemStateExp state condition = some (.word value)) :
    panSemEvaluateIfClauseRiscV64 evaluateProgram state condition thenBranch elseBranch =
      (if value = 0 then evaluateProgram elseBranch state
       else evaluateProgram thenBranch state) := by
  simp [panSemEvaluateIfClauseRiscV64, panSemTotalIfStep, heval]

theorem panSemEvaluateIfClauseRiscV64_eval_error
    (evaluateProgram : Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (condition : Exp (RiscV.Word 64))
    (thenBranch elseBranch : Prog (RiscV.Word 64))
    (heval : evalPanSemStateExp state condition = none) :
    panSemEvaluateIfClauseRiscV64 evaluateProgram state condition thenBranch elseBranch =
      (some .error, state) := by
  simp [panSemEvaluateIfClauseRiscV64, panSemTotalIfStep, heval]

theorem panSemEvaluateIfClauseRiscV64_eval_nonword
    (evaluateProgram : Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (condition : Exp (RiscV.Word 64))
    (thenBranch elseBranch : Prog (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExp state condition = some (.rStruct values)) :
    panSemEvaluateIfClauseRiscV64 evaluateProgram state condition thenBranch elseBranch =
      (some .error, state) := by
  simp [panSemEvaluateIfClauseRiscV64, panSemTotalIfStep, heval]

/-- The executed source evaluator's `Skip` projection is exactly the total
    `Skip` equation. -/
theorem panSemEvaluateCodeStateWithPostState_skip_total
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    (panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.skip : Prog α)).map panSemTotalOfExecuted = some (panSemEvaluateSkip state) := by
  rw [panSemEvaluateCodeStateWithPostState_skip]
  rfl

/-- The executed source evaluator's `Tick` projection is exactly the total
    `Tick` equation. -/
theorem panSemEvaluateCodeStateWithPostState_tick_total
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    (panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.tick : Prog α)).map panSemTotalOfExecuted = some (panSemEvaluateTick state) := by
  rw [panSemEvaluateCodeStateWithPostState_tick]
  by_cases hclock : state.clock = 0 <;>
    simp [panSemTotalOfExecuted, panSemEvaluateTick, panSemProgResultOfClockResult, hclock]

/-- The executed source evaluator's `Break` projection is the total HOL-shaped
    `Break` clause. -/
theorem panSemEvaluateCodeStateWithPostState_break_total
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    (panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.break : Prog α)).map panSemTotalOfExecuted = some (panSemEvaluateBreak state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    panSemTotalOfExecuted, panSemEvaluateBreak, panSemProgResultOfClockResult,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- The executed source evaluator's `Continue` projection is the total
    HOL-shaped `Continue` clause. -/
theorem panSemEvaluateCodeStateWithPostState_continue_total
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    (panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.continue : Prog α)).map panSemTotalOfExecuted =
      some (panSemEvaluateContinue state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    panSemTotalOfExecuted, panSemEvaluateContinue, panSemProgResultOfClockResult,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- HOL `fix_clock` (`cakeml/pancake/semantics/panSemScript.sml:446-449`): clamp
    a returned state's clock to the entry clock. -/
def panSemFixClock (entryClock : Nat) (state : PanSemState α (FfiState σ)) :
    PanSemState α (FfiState σ) :=
  { state with clock := min entryClock state.clock }

@[simp] theorem panSemFixClock_clock_le
    (entryClock : Nat) (state : PanSemState α (FfiState σ)) :
    (panSemFixClock entryClock state).clock ≤ entryClock := by
  exact Nat.min_le_left _ _

/-! A small source-program fragment gives the clock leaves, `Seq`, and `If`
    with `Const` or `Var Local` conditions a real recursive evaluator over the
    complete production state.  This is a total interpreter for the declared
    fragment only; it does not stand in for the full HOL `evaluate_def`, whose
    remaining expression-bearing and recursive constructors still need their
    faithful evaluator and clock/termination proofs. -/

/-- Source programs in the restricted fragment covered by the total
    clock-leaf/sequence/local-conditional evaluator. `toProg` embeds the
    fragment in the production syntax without changing its constructors. -/
inductive PanSemSeqFragment (α : Type u) where
  | leaf (leaf : PanSemClockLeaf)
  | seq (first second : PanSemSeqFragment α)
  | iteConst (condition : α)
      (thenBranch elseBranch : PanSemSeqFragment α)
  | iteLocal (condition : VarName)
      (thenBranch elseBranch : PanSemSeqFragment α)

/-- Embed a sequence/clock-leaf fragment into the production Pancake syntax. -/
def PanSemSeqFragment.toProg : PanSemSeqFragment α → Prog α
  | PanSemSeqFragment.leaf clockCtor => PanSemClockLeaf.toProg clockCtor
  | PanSemSeqFragment.seq prog1 prog2 => .seq prog1.toProg prog2.toProg
  | PanSemSeqFragment.iteConst condition thenBranch elseBranch =>
      .ite (.const condition) thenBranch.toProg elseBranch.toProg
  | PanSemSeqFragment.iteLocal condition thenBranch elseBranch =>
      .ite (.var .local condition) thenBranch.toProg elseBranch.toProg

/-- Total recursive HOL-result evaluator for the sequence/clock-leaf/local-If
    fragment.
    Its result is HOL's `result option × state`; the `Option` is the semantic
    result option from `evaluate_def`, not evaluator failure or fuel exhaustion.
    The recursive calls are on the source subprograms, and `Seq` clamps the
    first post-state clock before evaluating its second subprogram. For `If`,
    the condition subgrammar covers `Const` and direct `Var Local`; a missing or
    non-word local returns HOL's `Error` result with the complete state
    unchanged. This restricted interpreter is untagged and does not claim the
    whole-program `evaluate_def` port. -/
def panSemEvaluateSeqFragment [DecidableEq α] [OfNat α 0]
    (program : PanSemSeqFragment α)
    (state : PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match program with
  | .leaf leaf => panSemEvaluateClockLeaf leaf state
  | .seq first second =>
      let (result, firstState) := panSemEvaluateSeqFragment first state
      let fixedState := panSemFixClock state.clock firstState
      match result with
      | none => panSemEvaluateSeqFragment second fixedState
      | some result => (some result, fixedState)
  | .iteConst condition thenBranch elseBranch =>
      if condition = 0 then
        panSemEvaluateSeqFragment elseBranch state
      else
        panSemEvaluateSeqFragment thenBranch state
  | .iteLocal condition thenBranch elseBranch =>
      match state.locals condition with
      | some (.word value) =>
          if value = 0 then
            panSemEvaluateSeqFragment elseBranch state
          else
            panSemEvaluateSeqFragment thenBranch state
      | _ => (some .error, state)

/-! A second restricted fragment makes the `If` condition an arbitrary source
    expression and evaluates it from the full RISC-V 64-bit `PanSemState`.
    Branch recursion remains structural, so this removes the callback boundary
    from the earlier `If` helper while still covering only clock leaves, `Seq`,
    and `If`; it is not the full `evaluate_def` over `Prog`. -/

/-- RISC-V 64-bit source-program fragment with unrestricted `Exp` conditions
    on its recursive `If` constructor. This is a support fragment rather than
    an exact port of HOL `prog`: it omits the other statement constructors and
    is specialized to the production RV64 word representation. -/
inductive PanSemExprIfFragmentRiscV64 where
  | leaf (leaf : PanSemClockLeaf)
  | seq (first second : PanSemExprIfFragmentRiscV64)
  | ite (condition : Exp (RiscV.Word 64))
      (thenBranch elseBranch : PanSemExprIfFragmentRiscV64)
  deriving Repr

/-- Embed the restricted expression-If fragment into production Pancake syntax. -/
def PanSemExprIfFragmentRiscV64.toProg :
    PanSemExprIfFragmentRiscV64 → Prog (RiscV.Word 64)
  | PanSemExprIfFragmentRiscV64.leaf clockCtor => PanSemClockLeaf.toProg clockCtor
  | PanSemExprIfFragmentRiscV64.seq first second => .seq first.toProg second.toProg
  | PanSemExprIfFragmentRiscV64.ite condition thenBranch elseBranch =>
      .ite condition thenBranch.toProg elseBranch.toProg

/-- Total recursive RV64 evaluator for clock leaves, `Seq`, and `If` with any
    `Exp` condition. It evaluates the condition through `evalPanSemStateExp`
    using the complete state and recursively evaluates the chosen branch in
    that same state. A missing or non-word result returns `(some Error, state)`.
    The evaluator has no branch callback or evaluator-fuel `Option`; the
    remaining `Prog` constructors and HOL-polymorphic word carrier are outside
    this fragment, so it remains untagged and does not close the full
    `evaluate_def` port. -/
def panSemEvaluateExprIfFragmentRiscV64 [NeZero 64]
    [BEq (RiscV.Word 64)] [DecidableEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (program : PanSemExprIfFragmentRiscV64)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  match program with
  | PanSemExprIfFragmentRiscV64.leaf clockCtor =>
      panSemEvaluateClockLeaf clockCtor state
  | PanSemExprIfFragmentRiscV64.seq first second =>
      let (result, firstState) := panSemEvaluateExprIfFragmentRiscV64 first state
      let fixedState := panSemFixClock state.clock firstState
      match result with
      | none => panSemEvaluateExprIfFragmentRiscV64 second fixedState
      | some result => (some result, fixedState)
  | PanSemExprIfFragmentRiscV64.ite condition thenBranch elseBranch =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then
            panSemEvaluateExprIfFragmentRiscV64 elseBranch state
          else
            panSemEvaluateExprIfFragmentRiscV64 thenBranch state
      | _ => (some .error, state)

/-! ## Compositional `Seq` step

    HOL `Seq` (`cakeml/pancake/semantics/panSemScript.sml:615-618`) fixes the
    clock of the first command's result and continues with the second command
    only on a normal completion.  This is exposed as a compositional helper over
    an already evaluated first `(result, state)` pair and a continuation for the
    second command: it is not a whole-program evaluator and has no default
    branch for unimplemented constructors. -/

/-- HOL `Seq` composition: given the evaluated first command's `(result, state)`
    pair and a continuation for the second command, clamp the first state's
    clock to the entry clock (`fix_clock`) and run the continuation only on a
    normal completion; otherwise return the first outcome with the clamped
    state. -/
def panSemTotalSeqStep
    (entryClock : Nat)
    (firstResult : PanSemProgResult α σ) (firstState : PanSemState α (FfiState σ))
    (continueSecond :
      PanSemState α (FfiState σ) → PanSemProgResult α σ × PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  let fixedState := panSemFixClock entryClock firstState
  match firstResult with
  | .normal => continueSecond fixedState
  | other => (other, fixedState)

@[simp] theorem panSemTotalSeqStep_normal
    (entryClock : Nat) (firstState : PanSemState α (FfiState σ))
    (continueSecond :
      PanSemState α (FfiState σ) → PanSemProgResult α σ × PanSemState α (FfiState σ)) :
    panSemTotalSeqStep entryClock .normal firstState continueSecond =
      continueSecond (panSemFixClock entryClock firstState) := rfl

theorem panSemTotalSeqStep_of_ne_normal
    (entryClock : Nat) (firstResult : PanSemProgResult α σ)
    (firstState : PanSemState α (FfiState σ))
    (continueSecond :
      PanSemState α (FfiState σ) → PanSemProgResult α σ × PanSemState α (FfiState σ))
    (h : firstResult ≠ .normal) :
    panSemTotalSeqStep entryClock firstResult firstState continueSecond =
      (firstResult, panSemFixClock entryClock firstState) := by
  cases firstResult <;> simp_all [panSemTotalSeqStep]

/-! ## Compositional Assign step

HOL `Assign` (`panSemScript.sml:566-572`) evaluates the source, requires
`is_valid_value`, writes through `set_kvar`, and returns `(SOME Error, s)`
unchanged when the source fails or the destination is invalid.  Faithful source
evaluation is a separate obligation: HOL `panSem$eval` reads memory through the
source state's `memaddrs`, endianness, and byte width for `Load`/`Load32`/
`LoadByte`/`Op`, whereas the legacy `evalPanValueExp` default does not.  Until
that faithful evaluator is connected here, this file keeps only the exact
post-evaluation composition: given the already evaluated source result, apply
HOL's validity check and binding update.  No other `Prog` constructor is given a
fallback. -/

def panSemTotalAssignStep
    [BEq α] (state : PanSemState α (FfiState σ)) (kind : VarKind) (name : VarName)
    (evaluated : Option (PanValue α)) : PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  match evaluated with
  | none => (.error, state)
  | some value =>
      if panValueAssignmentValid state.structs state.locals state.globals kind name value then
        match kind with
        | .local =>
            (.normal, { state with locals := updatePanValueMap state.locals name value })
        | .global =>
            (.normal, { state with globals := updatePanValueMap state.globals name value })
      else (.error, state)

theorem panSemTotalAssignStep_none
    [BEq α] (state : PanSemState α (FfiState σ)) (kind : VarKind) (name : VarName) :
    panSemTotalAssignStep state kind name none = (.error, state) := rfl

theorem panSemTotalAssignStep_normal_local
    [BEq α] (state : PanSemState α (FfiState σ)) (name : VarName) (evaluated : PanValue α)
    (h : panValueAssignmentValid state.structs state.locals state.globals .local name evaluated = true) :
    panSemTotalAssignStep state .local name (some evaluated) =
      (.normal, { state with locals := updatePanValueMap state.locals name evaluated }) := by
  simp [panSemTotalAssignStep, h]

theorem panSemTotalAssignStep_normal_global
    [BEq α] (state : PanSemState α (FfiState σ)) (name : VarName) (evaluated : PanValue α)
    (h : panValueAssignmentValid state.structs state.locals state.globals .global name evaluated = true) :
    panSemTotalAssignStep state .global name (some evaluated) =
      (.normal, { state with globals := updatePanValueMap state.globals name evaluated }) := by
  simp [panSemTotalAssignStep, h]

theorem panSemTotalAssignStep_invalid
    [BEq α] (state : PanSemState α (FfiState σ)) (kind : VarKind) (name : VarName)
    (evaluated : PanValue α)
    (h : panValueAssignmentValid state.structs state.locals state.globals kind name evaluated = false) :
    panSemTotalAssignStep state kind name (some evaluated) = (.error, state) := by
  simp [panSemTotalAssignStep, h]

end Flapjack
