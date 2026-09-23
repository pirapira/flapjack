import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Semantics.PanSem

/-!
Source-state conversion and evaluator support for porting HOL
`pan_structsProofScript.sml` `compile_correct`. The full theorem's premises
and invariant postconditions are not yet proved here.
-/

namespace Flapjack

mutual
  /-- Executable counterpart of HOL `convert_v_def`. `PanValue.word`
      represents HOL `Val (Word w)` directly; named record fields are
      recursively converted in order and their labels are dropped. Its direct
      HOL-EVAL regression is recorded in the adjacent probe fixture. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_v_def"]
  def panStructConvertValue : PanValue α → PanValue α
    | .word value => .word value
    | .rStruct fields => .rStruct (panStructConvertValues fields)
    | .nStruct _ fields => .rStruct (panStructConvertFieldValues fields)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertValues : List (PanValue α) → List (PanValue α)
    | [] => []
    | value :: values => panStructConvertValue value :: panStructConvertValues values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructConvertFieldValues : List (FieldName × PanValue α) → List (PanValue α)
    | [] => []
    | (_, value) :: fields =>
        panStructConvertValue value :: panStructConvertFieldValues fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Executable counterpart of HOL `v_flds_ok_def` over `PanValue`.
      Named-record field names, order, and recursively computed shapes are all
      checked as in the HOL definition. Lean `StructInfo` carries a `size`
      field absent from the HOL context projection; this predicate reads only
      `.fields`, as HOL does. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_def"]
  def panStructValueFieldsOk [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesFieldsOk structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOk structs fields ∧
          match lookupInfo name structs with
          | none => False
          | some info =>
              fields.map Prod.fst = info.fields.map Prod.fst ∧
                fields.map (panSemShapeOf ∘ Prod.snd) = info.fields.map Prod.snd
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOk [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueFieldsOk structs value ∧ panStructValuesFieldsOk structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOk [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueFieldsOk structs value ∧ panStructFieldValuesFieldsOk structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Executable counterpart of HOL `is_wf_shape_v_def` over `PanValue`.
      Lean `StructInfo` carries a `size` field absent from the HOL context
      projection; this predicate checks only name membership and nested values,
      as HOL does. -/
  @[hol "cakeml/pancake/semantics/panPropsScript.sml" "is_wf_shape_v_def"]
  def panStructValueShapeWf [BEq String] (structs : StructContext) :
      PanValue α → Prop
    | .word _ => True
    | .rStruct values => panStructValuesShapeWf structs values
    | .nStruct name fields =>
        (lookupInfo name structs ≠ none) ∧ panStructFieldValuesShapeWf structs fields
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesShapeWf [BEq String] (structs : StructContext) :
      List (PanValue α) → Prop
    | [] => True
    | value :: values =>
        panStructValueShapeWf structs value ∧ panStructValuesShapeWf structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesShapeWf [BEq String] (structs : StructContext) :
      List (FieldName × PanValue α) → Prop
    | [] => True
    | (_, value) :: fields =>
        panStructValueShapeWf structs value ∧ panStructFieldValuesShapeWf structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- FEVERY adapters for PanSemState's total lookup functions. The shape-map
    premise below supplies finite support, so these universal clauses are the
    function-view translation of the HOL finite-map predicates. -/
def panStructEveryValueFieldsOk [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueFieldsOk structs value

def panStructEveryValueShapeWf [BEq String] (structs : StructContext)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value → panStructValueShapeWf structs value

/-- Pointwise view of the HOL equation
    `alist_to_fmap ctxt = FMAP_MAP2 (shape_of o SND) values`. This equality
    checks both lookup values and finite support. -/
def panStructShapeMapEq [BEq String] (shapes : InfoMap Shape)
    (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name, lookupInfo name shapes = (values name).map panSemShapeOf

def panStructContextShapeView (structs : StructContext) :
    List (StructName × InfoMap Shape) :=
  structs.map fun (name, info) => (name, info.fields)

/-- Executable list-map counterpart of HOL `convert_code_def`. It converts
    each source-owned code entry and uses the original parameter shapes while
    compiling the body, as HOL does with `ctxt with locals := params`.
    This is intentionally untagged: HOL maps a finite map with unique keys,
    while `PanSemCodeMap` is an `InfoMap` list which may contain duplicate
    keys; this definition maps every list entry and cannot express HOL's
    finite-map domain invariant. -/
def panStructConvertCode [BEq String] (context : StructPassContext)
    (code : PanSemCodeMap α) : PanSemCodeMap α :=
  code.map fun (name, (parameters, body, returnShape)) =>
    (name,
      (parameters.map fun (parameter, shape) =>
          (parameter, structCompileShape context.structs shape),
        structCompileProg { context with locals := parameters } body,
        structCompileShape context.structs returnShape))

/-- Executable projection of HOL `convert_s_def` over `PanSemState`.
    The `structs` update and value conversion follow HOL; `code` is projected
    through the list-map helper above, and exception shapes through a total
    lookup function. This is intentionally untagged: `locals`, `globals`, and
    exception shapes are total lookup functions rather than finite maps, while
    code is an `InfoMap` list that may have duplicate keys. These interfaces
    cannot express HOL finite-map support or its exact `FMAP_MAP2` equations.
    The faithful finite-map state conversion remains open. -/
def panStructConvertState [BEq String] (context : StructPassContext)
    (state : PanSemState α ffi) : PanSemState α ffi where
  locals := fun name => (state.locals name).map panStructConvertValue
  globals := fun name => (state.globals name).map panStructConvertValue
  structs := []
  code := panStructConvertCode context state.code
  exceptionShapes := fun exception =>
    (state.exceptionShapes exception).map (structCompileShape context.structs)
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddress := state.baseAddress
  topAddress := state.topAddress

def panStructConvertLocalMap (locals : VarName → Option (PanValue α)) :=
  fun name => (locals name).map panStructConvertValue

def panStructConvertControlResult : PanValueFfiControlResult α σ →
    PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .returned locals globals memory ffi values =>
      .returned (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi (panStructConvertValues values)
  | .raised locals globals memory ffi exception value =>
      .raised (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi exception (panStructConvertValue value)
  | .broke locals globals memory ffi =>
      .broke (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .continued locals globals memory ffi =>
      .continued (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .finalFfi locals globals memory ffi event =>
      .finalFfi (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi event

def panStructConvertClockOutcome : PanValueFfiClockOutcome α σ →
    PanValueFfiClockOutcome α σ
  | .control result => .control (panStructConvertControlResult result)
  | .timeout locals globals memory ffi =>
      .timeout (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi

def panStructConvertClockResult (result : PanValueFfiClockResult α σ) :
    PanValueFfiClockResult α σ :=
  (panStructConvertClockOutcome result.1, result.2)

@[simp] theorem panStructConvertState_code [BEq String]
    (context : StructPassContext) (state : PanSemState α ffi) :
    (panStructConvertState context state).code =
      panStructConvertCode context state.code := rfl

@[simp] theorem panStructCompileSkip_eq_skip [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.skip : Prog α) = .skip := by
  simp [structCompileProg]

/-- Evaluator-equation support for a future HOL `compile_correct` Skip case:
    this proves only the two source/converted outcomes and omits the HOL
    theorem's premises and value/shape-map postconditions, so it is not an
    induction case port and intentionally has no `@[hol]` tag. -/
theorem panStructSkipEvaluatorSupport
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.skip : Prog α) =
      some ((.control (.normal state.locals state.globals state.memory state.ffi),
          state.clock), state) ∧
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal (panStructConvertState context state).locals
          (panStructConvertState context state).globals
          (panStructConvertState context state).memory
          (panStructConvertState context state).ffi),
        (panStructConvertState context state).clock),
        panStructConvertState context state) := by
  constructor
  · exact panSemEvaluateCodeStateWithPostState_skip
      evaluationContext primitive handler bytesInWord state
  · simpa [structCompileProg] using
      (panSemEvaluateCodeStateWithPostState_skip
        evaluationContext primitive handler bytesInWord
        (panStructConvertState context state))

@[simp] theorem panStructCompileTick_eq_tick [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.tick : Prog α) = .tick := by
  simp [structCompileProg]

/-- Evaluator-equation support for a future HOL `compile_correct` Tick case:
    the source and compiled executions agree after the current conversion in
    both clock branches, but the HOL theorem's hypotheses and invariant
    postconditions are not included. This is not an induction case port and
    intentionally has no `@[hol]` tag. -/
theorem panStructTickEvaluatorSupport
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertState context state)
        (structCompileProg context (.tick : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.tick : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  by_cases hclock : state.clock = 0
  · simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
      panStructConvertState, panStructConvertClockResult,
      panStructConvertClockOutcome, hclock]
    constructor <;> funext name <;> rfl
  · simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
      panStructConvertState, panStructConvertClockResult,
      panStructConvertClockOutcome, hclock]
    congr 1 <;> funext name <;> rfl

end Flapjack
