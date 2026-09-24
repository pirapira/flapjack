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
* `panSemEvaluateSkip` and `panSemEvaluateTick` are base-case infrastructure
  for the eventual evaluator, not yet the single total recursive
  `panSemEvaluate`.

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

/-- HOL `fix_clock` (`cakeml/pancake/semantics/panSemScript.sml:446-449`): clamp
    a returned state's clock to the entry clock. -/
def panSemFixClock (entryClock : Nat) (state : PanSemState α (FfiState σ)) :
    PanSemState α (FfiState σ) :=
  { state with clock := min entryClock state.clock }

/-! ## Genuine total recursive evaluator (staged)

    `panSemTotalEvaluate` is a single total function returning the HOL
    `(result option # state)` shape with no fuel.  It currently implements the
    control-flow constructors `Skip`, `Tick`, `Seq`, `Break`, `Continue`, and
    `Annot` exactly; every other constructor is a documented staging
    placeholder returning `.error` with the state unchanged, NOT HOL semantics.
    The recursive `Seq` equations are direct; the evaluator will move to the
    HOL lexicographic measure `(state.clock, program size)` when the
    clock-recursive `While`/`Call`/`DecCall` constructors are added. -/

/-- Total source evaluator, staged over the `Prog` constructors. -/
def panSemTotalEvaluate (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) (program : Prog α) :
    PanSemProgResult α σ × PanSemState α (FfiState σ) :=
  match program with
  | .skip => panSemEvaluateSkip state
  | .tick => panSemEvaluateTick state
  | .seq first second =>
      let firstStep := panSemTotalEvaluate context primitive handler bytesInWord state first
      let secondState := panSemFixClock state.clock firstStep.2
      match firstStep.1 with
      | .normal => panSemTotalEvaluate context primitive handler bytesInWord secondState second
      | other => (other, secondState)
  | .break => (.broke, state)
  | .continue => (.continued, state)
  | .annot _ _ => (.normal, state)
  | _ => (.error, state)

@[simp] theorem panSemTotalEvaluate_skip
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.skip : Prog α) =
      (.normal, state) := rfl

@[simp] theorem panSemTotalEvaluate_tick
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.tick : Prog α) =
      (if state.clock = 0 then
        (.timeout, { state with locals := fun _ => none })
       else
        (.normal, { state with clock := state.clock - 1 })) := rfl

@[simp] theorem panSemTotalEvaluate_break
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.break : Prog α) =
      (.broke, state) := rfl

@[simp] theorem panSemTotalEvaluate_continue
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.continue : Prog α) =
      (.continued, state) := rfl

@[simp] theorem panSemTotalEvaluate_annot
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) (tag text : String) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.annot tag text : Prog α) =
      (.normal, state) := rfl

/-- The `Seq` equation is the HOL one: evaluate the first command, clamp the
    returned clock to the entry clock (`fix_clock`), continue with the second
    command only on a normal completion, and otherwise return the first
    outcome with the clamped state (`panSemScript.sml:615-618`). -/
theorem panSemTotalEvaluate_seq
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) (first second : Prog α) :
    panSemTotalEvaluate context primitive handler bytesInWord state (.seq first second) =
      (match panSemTotalEvaluate context primitive handler bytesInWord state first with
       | (.normal, firstState) =>
           panSemTotalEvaluate context primitive handler bytesInWord
             (panSemFixClock state.clock firstState) second
       | (other, firstState) => (other, panSemFixClock state.clock firstState)) := by
  simp only [panSemTotalEvaluate]
  cases h : panSemTotalEvaluate context primitive handler bytesInWord state first with
  | mk r s => cases r <;> rfl

end Flapjack
