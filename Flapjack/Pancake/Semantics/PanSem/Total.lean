import Flapjack.Pancake.Semantics.PanSem

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

* `PanSemProgResult` is an isomorphic in-Lean encoding of HOL's
  `result option`: `PanSemProgResult.normal` encodes HOL's `NONE`, so it is
  equivalent to `result option` but not literally that type;
* `panSemProgResultOfClockResult` maps the executed clocked result onto it;
* `panSemEvaluateSkip`, `panSemEvaluateBreak`, `panSemEvaluateContinue`, and
  `panSemEvaluateTick` are base-case infrastructure
  for the eventual evaluator, not yet the single total recursive
  `panSemEvaluate`;
* `panSemTotalSeqStep` is the HOL `Seq` composition (clamp the first result's
  clock with `fix_clock`, continue only on a normal completion) as a helper over
  an already evaluated first pair and a continuation, not a whole-program
  evaluator.

The state half is the production `PanSemState`, so the eventual total
`panSemEvaluate` returns a `PanSemProgResult α σ × PanSemState α (FfiState σ)`
pair with no `Option`/fuel wrapper, recursing on the HOL termination measure
`(state.clock, program size)`.  `panSemTotalOfExecuted` is only a proved
relation between the executed evaluator and this interface; it never defines
total evaluation.  Everything here is untagged until that total evaluator and
its exact HOL statement are established.
-/

namespace Flapjack

/-- Isomorphic in-Lean encoding of HOL `panSemScript.sml:68-75` `result option`:
    `normal` encodes HOL `NONE` (normal completion); the other constructors
    encode the corresponding `SOME` payloads. -/
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

/-- Turn an executed `(clocked result, state)` pair into the HOL-shaped
    `(result, state)` pair.  This is a proved relation between the executed
    evaluator and the total interface only; it is not part of the definition of
    total evaluation. -/
def panSemTotalOfExecuted
    (pair : PanValueFfiClockResult α σ × PanSemState α (FfiState σ)) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  (panSemProgResultOfClockResult pair.1, pair.2)

/-! ## Base-case total equations

    Base-case infrastructure for the eventual single total recursive
    `panSemEvaluate`; these functions are not that evaluator yet.  They return
    the HOL `(result option # state)` shape directly (no `Option`/fuel
    wrapper), and the theorems below relate them to the executed source
    evaluator's `(result, state)` projection via the proved relation
    `panSemTotalOfExecuted`. -/

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
