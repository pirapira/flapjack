import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem

/-!
Source-state conversion and evaluator support for porting HOL
`pan_structsProofScript.sml` `compile_correct`. The full theorem's premises
and invariant postconditions are not yet proved here.
-/

namespace Flapjack

mutual
  /-- Exact executable counterpart of HOL `convert_v_def`. The HOL datatype
      cases are `Val (Word w)`, `RStruct xs`, and `NStruct nm flds`; these
      correspond respectively to `.word`, `.rStruct`, and `.nStruct` in
      `PanValue`. The first case is unchanged, the second maps recursively in
      order, and the third drops both record and field names while recursively
      mapping field values in order. The direct HOL-EVAL regression is recorded
      in the adjacent probe fixture. -/
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

/-! Structural Bool equality for the translated Shape datatype. It performs
    the HOL constructor equality cases recursively and avoids a BEq instance
    for Shape or String. -/
mutual
  def panStructShapeEqBool : Shape → Shape → Bool
    | .one, .one => true
    | .comb left, .comb right => panStructShapeListEqBool left right
    | .named left, .named right => decide (left = right)
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructShapeListEqBool : List Shape → List Shape → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        panStructShapeEqBool left right && panStructShapeListEqBool lefts rights
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Exact Bool-valued counterpart of HOL `v_flds_ok_def`. The Lean
      `StructInfo` includes HOL's `fields` and `size`, plus a Flapjack-only
      `shapedFields` cache which is ignored here. Key lookup uses decidable
      equality and first-match order, matching HOL `ALOOKUP`; structural shape
      list equality is decided by a structural comparator equivalent to HOL
      structural list equality. -/
  @[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_def"]
  def panStructValueFieldsOkBool (structs : StructContext) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panStructValuesFieldsOkBool structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOkBool structs fields &&
          match panPropsALookupEq name structs with
          | none => false
          | some info =>
              decide (fields.map Prod.fst = info.fields.map Prod.fst) &&
              panStructShapeListEqBool
                (fields.map (panSemShapeOf ∘ Prod.snd)) (info.fields.map Prod.snd)
  termination_by value => sizeOf value
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructValuesFieldsOkBool (structs : StructContext) :
      List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panStructValueFieldsOkBool structs value &&
          panStructValuesFieldsOkBool structs values
  termination_by values => sizeOf values
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panStructFieldValuesFieldsOkBool (structs : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panStructValueFieldsOkBool structs value &&
          panStructFieldValuesFieldsOkBool structs fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Prop-valued Flapjack convenience predicate mirroring HOL
      `v_flds_ok_def`. It is not an exact port: HOL returns Bool, while this
      declaration returns Prop and uses `[BEq String]` lookup. The adjacent
      `panStructValueFieldsOkBool` definition is the Bool/equality-based HOL
      counterpart. `StructInfo.shapedFields` is an additional Lean cache field
      absent from HOL and is ignored by both predicates. -/
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
  /-- Prop-valued Flapjack convenience predicate mirroring HOL
      `is_wf_shape_v_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. The
      adjacent `panIsWfShapeValueBool` definition is the Bool/equality-based
      HOL counterpart. The HOL `struct_info` has fields and size; Lean adds an
      unused `shapedFields` cache which this predicate also ignores. -/
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

/-- Lookup in HOL's `FMAP_MAP2`-shaped `InfoMap` representation commutes with
    mapping values. Keeping this finite list, rather than only its total lookup
    function, preserves the exact support needed by `compile_correct`. -/
theorem lookupInfo_mapValues [BEq String] (entries : InfoMap α)
    (name : String) (convert : α → β) :
    lookupInfo name (entries.map fun (key, value) => (key, convert value)) =
      (lookupInfo name entries).map convert := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      by_cases hkey : key == name
      · simp [lookupInfo, hkey]
      · simp [lookupInfo, hkey, ih]

theorem panStruct_mapKeys_preserved (entries : InfoMap α)
    (transform : String × α → String × β)
    (htransform : ∀ entry, (transform entry).1 = entry.1) :
    (entries.map transform).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      simp [ih, htransform]

/-- A finite-map representation of the map-valued fields in HOL's
    `panSem$state`, together with its exact lookup view in the production
    `PanSemState` evaluator. `entries` are authoritative; the agreement fields
    make the evaluator's total functions exactly the corresponding finite-map
    lookup. `Nodup` records the key uniqueness inherent in HOL finite maps. -/
structure PanStructFiniteState [BEq String] (α : Type u) (ffi : Type v) where
  runtime : PanSemState α ffi
  locals : InfoMap (PanValue α)
  globals : InfoMap (PanValue α)
  exceptionShapes : InfoMap Shape
  locals_nodup : (locals.map Prod.fst).Nodup
  globals_nodup : (globals.map Prod.fst).Nodup
  exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup
  code_nodup : (runtime.code.map Prod.fst).Nodup
  locals_lookup : ∀ name, runtime.locals name = lookupInfo name locals
  globals_lookup : ∀ name, runtime.globals name = lookupInfo name globals
  exceptionShapes_lookup :
    ∀ name, runtime.exceptionShapes name = lookupInfo name exceptionShapes

/-- Build the production evaluator view from explicit HOL-shaped finite maps.
    The only side conditions are the key uniqueness conditions that are part
    of the finite-map representation itself; lookup agreement is constructed
    definitionally instead of being added as a theorem premise. -/
def panStructFiniteStateFromMaps [BEq String]
    (runtime : PanSemState α ffi)
    (locals globals : InfoMap (PanValue α)) (exceptionShapes : InfoMap Shape)
    (code : PanSemCodeMap α)
    (locals_nodup : (locals.map Prod.fst).Nodup)
    (globals_nodup : (globals.map Prod.fst).Nodup)
    (exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup)
    (code_nodup : (code.map Prod.fst).Nodup) : PanStructFiniteState α ffi where
  runtime := { runtime with
    locals := fun name => lookupInfo name locals
    globals := fun name => lookupInfo name globals
    exceptionShapes := fun name => lookupInfo name exceptionShapes
    code := code }
  locals := locals
  globals := globals
  exceptionShapes := exceptionShapes
  locals_nodup := locals_nodup
  globals_nodup := globals_nodup
  exceptionShapes_nodup := exceptionShapes_nodup
  code_nodup := code_nodup
  locals_lookup := by
    cases runtime
    intro name
    simp
  globals_lookup := by
    cases runtime
    intro name
    simp
  exceptionShapes_lookup := by
    cases runtime
    intro name
    simp

/-- Map all HOL finite-map fields while keeping the same finite key support.
    The result is again related to the production evaluator state by exact
    lookup equations. -/
def panStructConvertFiniteState [BEq String]
    (context : StructPassContext) (state : PanStructFiniteState α ffi) :
    PanStructFiniteState α ffi where
  runtime := panStructConvertState context state.runtime
  locals := state.locals.map fun (name, value) =>
    (name, panStructConvertValue value)
  globals := state.globals.map fun (name, value) =>
    (name, panStructConvertValue value)
  exceptionShapes := state.exceptionShapes.map fun (name, shape) =>
    (name, structCompileShape context.structs shape)
  locals_nodup := by
    rw [panStruct_mapKeys_preserved state.locals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.locals_nodup
    · intro entry
      rfl
  globals_nodup := by
    rw [panStruct_mapKeys_preserved state.globals
      (fun (name, value) => (name, panStructConvertValue value))]
    · exact state.globals_nodup
    · intro entry
      rfl
  exceptionShapes_nodup := by
    rw [panStruct_mapKeys_preserved state.exceptionShapes
      (fun (name, shape) => (name, structCompileShape context.structs shape))]
    · exact state.exceptionShapes_nodup
    · intro entry
      rfl
  code_nodup := by
    change ((panStructConvertCode context state.runtime.code).map Prod.fst).Nodup
    rw [show (panStructConvertCode context state.runtime.code).map Prod.fst =
        state.runtime.code.map Prod.fst by
          apply panStruct_mapKeys_preserved
          intro entry
          cases entry with
          | mk name value => rfl]
    exact state.code_nodup
  locals_lookup := by
    intro name
    simp [panStructConvertState, lookupInfo_mapValues, state.locals_lookup]
  globals_lookup := by
    intro name
    simp [panStructConvertState, lookupInfo_mapValues, state.globals_lookup]
  exceptionShapes_lookup := by
    intro name
    simp [panStructConvertState, lookupInfo_mapValues,
      state.exceptionShapes_lookup]

def panStructConvertLocalMap (locals : VarName → Option (PanValue α)) :=
  fun name => (locals name).map panStructConvertValue

def panStructConvertControlResult : PanValueFfiControlResult α σ →
    PanValueFfiControlResult α σ
  | .normal locals globals memory ffi =>
      .normal (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
        memory ffi
  | .error locals globals memory ffi =>
      .error (panStructConvertLocalMap locals) (panStructConvertLocalMap globals)
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

/-- The HOL-shaped Skip support theorem specialized to a state whose locals,
    globals, exception-shape map, and code all carry finite support and unique
    keys. This remains evaluator support: the full `compile_correct` premises
    and FEVERY/shape-map/result conclusions are not asserted here. -/
theorem panStructSkipFiniteMapEvaluatorSupport
    [BEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.skip : Prog α) =
      some ((.control (.normal state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime) ∧
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) := by
  simpa [panStructConvertFiniteState] using
    (panStructSkipEvaluatorSupport context evaluationContext primitive handler
      bytesInWord state.runtime)

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
