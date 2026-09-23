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
  /-- Bool-valued comparison for HOL `v_flds_ok_def`, using production
      `lookupInfo`. This is not currently tagged as an exact port: the HOL
      predicate uses HOL equality in `ALOOKUP`, while this declaration's
      lookup semantics are selected by `[BEq String]`; the equality adapter
      lemma only identifies lookup for lawful instances and does not establish
      that the production representation is the same HOL interface. Lean
      `StructInfo` also has an additional `shapedFields` cache absent from HOL.
      This Bool declaration is distinct from the Prop-valued convenience
      predicate below. -/
  def panStructValueFieldsOkBool (structs : StructContext) :
      PanValue α → Bool
    | .word _ => true
    | .rStruct values => panStructValuesFieldsOkBool structs values
    | .nStruct name fields =>
        panStructFieldValuesFieldsOkBool structs fields &&
          match lookupInfo name structs with
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
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `v_flds_ok_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
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
  /-- Prop-valued Flapjack convenience predicate mirroring the equations of
      HOL `is_wf_shape_v_def`. It is not an exact port: HOL returns Bool, while
      this declaration returns Prop and uses `[BEq String]` lookup. -/
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

/-- Function-view adapters of HOL's `FEVERY` premises for the Bool-valued
    PanStruct predicates. A `PanStructFiniteState` supplies the exact finite
    support and lookup relation for these production lookup functions. -/
def panStructEveryValueFieldsOkBool [BEq String]
    (structs : StructContext) (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value →
    panStructValueFieldsOkBool structs value = true

def panStructEveryValueShapeWfBool [BEq String]
    (structs : StructContext) (values : VarName → Option (PanValue α)) : Prop :=
  ∀ name value, values name = some value →
    panIsWfShapeValueBool structs value = true

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
    make locals, globals, and exception-shape lookup use HOL equality directly.
    The `LawfulBEq String` parameter ensures production code-map lookup agrees
    with equality-based HOL `FLOOKUP`. `Nodup` records the key uniqueness
    inherent in HOL finite maps. -/
structure PanStructFiniteState [BEq String] [LawfulBEq String]
    (α : Type u) (ffi : Type v) where
  runtime : PanSemState α ffi
  locals : InfoMap (PanValue α)
  globals : InfoMap (PanValue α)
  exceptionShapes : InfoMap Shape
  locals_nodup : (locals.map Prod.fst).Nodup
  globals_nodup : (globals.map Prod.fst).Nodup
  exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup
  code_nodup : (runtime.code.map Prod.fst).Nodup
  locals_lookup : ∀ name, runtime.locals name = panPropsALookupEq name locals
  globals_lookup : ∀ name, runtime.globals name = panPropsALookupEq name globals
  exceptionShapes_lookup :
    ∀ name, runtime.exceptionShapes name = panPropsALookupEq name exceptionShapes

/-- Build the production evaluator view from explicit HOL-shaped finite maps.
    The only side conditions are the key uniqueness conditions that are part
    of the finite-map representation itself; lookup agreement is constructed
    definitionally instead of being added as a theorem premise. -/
def panStructFiniteStateFromMaps [BEq String] [LawfulBEq String]
    (runtime : PanSemState α ffi)
    (locals globals : InfoMap (PanValue α)) (exceptionShapes : InfoMap Shape)
    (code : PanSemCodeMap α)
    (locals_nodup : (locals.map Prod.fst).Nodup)
    (globals_nodup : (globals.map Prod.fst).Nodup)
    (exceptionShapes_nodup : (exceptionShapes.map Prod.fst).Nodup)
    (code_nodup : (code.map Prod.fst).Nodup) : PanStructFiniteState α ffi where
  runtime := { runtime with
    locals := fun name => panPropsALookupEq name locals
    globals := fun name => panPropsALookupEq name globals
    exceptionShapes := fun name => panPropsALookupEq name exceptionShapes
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
def panStructConvertFiniteState [BEq String] [LawfulBEq String]
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
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.locals_lookup]
  globals_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues, state.globals_lookup]
  exceptionShapes_lookup := by
    intro name
    simp [panStructConvertState, panPropsALookupEq_mapValues,
      state.exceptionShapes_lookup]

@[simp] theorem panStructConvertFiniteState_locals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).locals.map Prod.fst =
      state.locals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_globals_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).globals.map Prod.fst =
      state.globals.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_exceptionShapes_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).exceptionShapes.map Prod.fst =
      state.exceptionShapes.map Prod.fst := by
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

@[simp] theorem panStructConvertFiniteState_code_support [BEq String]
    [LawfulBEq String] (context : StructPassContext)
    (state : PanStructFiniteState α ffi) :
    (panStructConvertFiniteState context state).runtime.code.map Prod.fst =
      state.runtime.code.map Prod.fst := by
  change (panStructConvertCode context state.runtime.code).map Prod.fst =
    state.runtime.code.map Prod.fst
  apply panStruct_mapKeys_preserved
  intro entry
  cases entry
  rfl

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

@[simp] theorem panStructCompileBreak_eq_break [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.break : Prog α) = .break := by
  simp [structCompileProg]

/-- Production source-state evaluator equation corresponding to HOL
    `evaluate (Break,s) = (SOME Break,s)`. -/
theorem panStructSourceBreakEvaluation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.break : Prog α) =
      some ((.control (.broke state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- Source/converted evaluator projection for production Break states. -/
theorem panStructBreakEvaluatorProjection
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
        (structCompileProg context (.break : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.break : Prog α)).map
    (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  rw [panStructCompileBreak_eq_break,
    panStructSourceBreakEvaluation evaluationContext primitive handler bytesInWord state,
    panStructSourceBreakEvaluation evaluationContext primitive handler bytesInWord
      (panStructConvertState context state)]
  simp [panStructConvertClockResult, panStructConvertClockOutcome,
    panStructConvertControlResult, panStructConvertState]
  constructor <;> rfl

/-- Full Break specialization of HOL `compile_correct`. Break is a continuing
    control result in HOL, so the unchanged source state preserves both field
    validity and both shape maps. This states all compile_correct
    postconditions over the finite-map wrapper and proves target evaluation
    from the source evaluator equation; it assumes no target result. It stays
    untagged because HOL has only the quantified theorem and Lean encodes
    `SOME Break` as a `.broke` clock outcome. -/
theorem panStructCompileCorrectBreakCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceBreak : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.break : Prog α) =
        some ((.control (.broke state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.break : Prog α)) =
      some ((.control (.broke
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructBreakEvaluatorProjection context evaluationContext
    primitive handler bytesInWord state.runtime
  rw [hsourceBreak] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.break : Prog α)) =
        some ((.control (.broke
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

@[simp] theorem panStructCompileContinue_eq_continue [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.continue : Prog α) = .continue := by
  simp [structCompileProg]

/-- Production source evaluator equation corresponding to HOL
    `evaluate (Continue,s) = (SOME Continue,s)`. -/
theorem panStructSourceContinueEvaluation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.continue : Prog α) =
      some ((.control (.continued state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-- Source/converted evaluator projection for production Continue states. -/
theorem panStructContinueEvaluatorProjection
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
        (structCompileProg context (.continue : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state (.continue : Prog α)).map
    (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) := by
  rw [panStructCompileContinue_eq_continue,
    panStructSourceContinueEvaluation evaluationContext primitive handler bytesInWord state,
    panStructSourceContinueEvaluation evaluationContext primitive handler bytesInWord
      (panStructConvertState context state)]
  simp [panStructConvertClockResult, panStructConvertClockOutcome,
    panStructConvertControlResult, panStructConvertState]
  constructor <;> rfl

/-- Full Continue specialization of HOL `compile_correct` over finite-map
    state. The unchanged source state preserves both field-validity clauses
    and both shape maps, and the result-value obligations are empty. It uses
    the source evaluation equation and proves target evaluation itself. This
    stays untagged because HOL has only the quantified theorem and encodes
    `SOME Continue` as Lean's `.continued` clock outcome. -/
theorem panStructCompileCorrectContinueCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceContinue : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.continue : Prog α) =
        some ((.control (.continued state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.continue : Prog α)) =
      some ((.control (.continued
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructContinueEvaluatorProjection context evaluationContext
    primitive handler bytesInWord state.runtime
  rw [hsourceContinue] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.continue : Prog α)) =
        some ((.control (.continued
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

/-- Private lookup bridge used by the Var proof below. This comment documents
    only this helper; the declaration-local HOL mismatch note for
    `panStructCompileExpCorrectVarCase` is placed immediately before that
    theorem. -/
private theorem lookupInfoStringDefault_eq_panPropsALookupEq
    {β : Type} (key : String) (entries : List (String × β)) :
    @lookupInfo String β instBEqOfDecidableEq key entries =
      panPropsALookupEq key entries := by
  letI : LawfulBEq String := instLawfulBEqString
  exact lookupInfo_eq_panPropsALookupEq key entries

/-- Documentation for `panStructCompileExpCorrectVarCase`: this is a derived
    Local/Global Var-constructor specialization of HOL `compile_exp_correct`;
    intentionally untagged because HOL has only the
    universally quantified theorem, not a separately named Var-case
    declaration. This Lean statement is not an exact statement port. It keeps
    successful source evaluation, but re-encodes the HOL premises: the direct
    `ctxt.structs = MAP ... s.structs` equality is replaced by equality of
    shape views (which observes names and fields, not the full Lean struct-info
    records); finite-map `FEVERY` field-validity is expressed as pointwise Bool
    predicates over total runtime lookups; and the `FMAP_MAP2` premises are
    expressed through pointwise shape-map adapters. The state wrapper supplies
    nodup `InfoMap` lists and lookup equations, while lawful `BEq String` is
    needed to align production lookup with HOL equality. The theorem carries
    `structInfosOk` as a premise, but this Var-case proof does not use it. Lean
    also stores a `shapedFields` cache absent from HOL, which these premises do
    not inspect, and its evaluator takes an explicit `bytesInWord` parameter.
    Its three conclusions are the Var instance of HOL's old-shape,
    `v_flds_ok`, and converted-evaluation conclusions. Other expression
    constructors remain open. -/
theorem panStructCompileExpCorrectVarCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (state : PanStructFiniteState α ffi)
    (bytesInWord : α)
    (name : VarName) (kind : VarKind) (value : PanValue α)
    (heval : evalPanValueExp state.runtime.structs state.runtime.locals
      state.runtime.globals state.runtime.memory state.runtime.baseAddress
      state.runtime.topAddress bytesInWord (.var kind name) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    structOldExpShape (α := α) context (.var kind name) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.runtime.structs value = true ∧
    evalPanValueExp (panStructConvertFiniteState context state).runtime.structs
      (panStructConvertFiniteState context state).runtime.locals
      (panStructConvertFiniteState context state).runtime.globals
      (panStructConvertFiniteState context state).runtime.memory
      (panStructConvertFiniteState context state).runtime.baseAddress
      (panStructConvertFiniteState context state).runtime.topAddress
      bytesInWord (structCompileExp (α := α) context (.var kind name)) =
        some (panStructConvertValue value) := by
  cases kind with
  | «local» =>
      have hlookup : state.runtime.locals name = some value := by
        simpa [evalPanValueExp] using heval
      have hshapeMap : panPropsALookupEq name context.locals = some (panSemShapeOf value) := by
        rw [← lookupInfo_eq_panPropsALookupEq, hlocalsMap name, hlookup]
        rfl
      have hshapeLookup :
          @lookupInfo String Shape instBEqOfDecidableEq name context.locals =
            some (panSemShapeOf value) := by
        rw [lookupInfoStringDefault_eq_panPropsALookupEq, hshapeMap]
      refine ⟨?_, hlocalsFields name value hlookup, ?_⟩
      · simp only [structOldExpShape]
        simpa using congrArg (fun result : Option Shape => result.getD .one) hshapeLookup
      · simp [evalPanValueExp, structCompileExp, panStructConvertFiniteState,
          panStructConvertState, hlookup]
  | «global» =>
      have hlookup : state.runtime.globals name = some value := by
        simpa [evalPanValueExp] using heval
      have hshapeMap : panPropsALookupEq name context.globals = some (panSemShapeOf value) := by
        rw [← lookupInfo_eq_panPropsALookupEq, hglobalsMap name, hlookup]
        rfl
      have hshapeLookup :
          @lookupInfo String Shape instBEqOfDecidableEq name context.globals =
            some (panSemShapeOf value) := by
        rw [lookupInfoStringDefault_eq_panPropsALookupEq, hshapeMap]
      refine ⟨?_, hglobalsFields name value hlookup, ?_⟩
      · simp only [structOldExpShape]
        simpa using congrArg (fun result : Option Shape => result.getD .one) hshapeLookup
      · simp [evalPanValueExp, structCompileExp, panStructConvertFiniteState,
          panStructConvertState, hlookup]

/-- Derived Const-constructor specialization of HOL `compile_exp_correct`.
    This stays untagged because HOL has only the universally quantified
    theorem, not a separately named Const-case declaration. As in the Var
    case above, the context equality uses a fields shape-view, finite-map
    FEVERY becomes pointwise Bool validity over total lookups, and FMAP_MAP2
    uses pointwise shape-map adapters backed by PanStructFiniteState's nodup
    lists. Lawful `BEq String` aligns production lookup with HOL equality.
    The theorem carries but does not use the translated struct-info premise. -/
theorem panStructCompileExpCorrectConstCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (state : PanStructFiniteState α ffi)
    (bytesInWord : α)
    (constant : α) (value : PanValue α)
    (heval : evalPanValueExp state.runtime.structs state.runtime.locals
      state.runtime.globals state.runtime.memory state.runtime.baseAddress
      state.runtime.topAddress bytesInWord (.const constant) = some value)
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (_hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (_hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (_hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    structOldExpShape (α := α) context (.const constant) = panSemShapeOf value ∧
    panStructValueFieldsOkBool state.runtime.structs value = true ∧
    evalPanValueExp (panStructConvertFiniteState context state).runtime.structs
      (panStructConvertFiniteState context state).runtime.locals
      (panStructConvertFiniteState context state).runtime.globals
      (panStructConvertFiniteState context state).runtime.memory
      (panStructConvertFiniteState context state).runtime.baseAddress
      (panStructConvertFiniteState context state).runtime.topAddress
      bytesInWord (structCompileExp (α := α) context (.const constant)) =
        some (panStructConvertValue value) := by
  cases value with
  | word wordValue =>
      have hword : constant = wordValue := by
        simpa [evalPanValueExp] using heval
      subst wordValue
      refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
      · simp [panStructValueFieldsOkBool]
      · simp [evalPanValueExp, panStructConvertFiniteState,
          panStructConvertState, panStructConvertValue]
  | rStruct values => simp [evalPanValueExp] at heval
  | nStruct name fields => simp [evalPanValueExp] at heval

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
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
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

/-- Exact production-evaluator projection for HOL-shaped finite-map state on
    Skip. Converting the source execution's clock result and post-state yields
    the execution of the converted state and compiled program. The state
    wrapper carries finite support and lookup agreement, so the projection does
    not assume a separate finite-support premise. -/
theorem panStructFiniteMapSkipEvaluationProjection
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.skip : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result, panStructConvertState context postState)) := by
  simp [panSemEvaluateCodeStateWithPostState_skip,
    panStructConvertFiniteState, panStructConvertState, panStructConvertClockResult,
    panStructConvertClockOutcome, panStructConvertControlResult]
  constructor <;> rfl

/-- Full Skip case of HOL `compile_correct`, specialized to the production
    `PanSemState` evaluator with the finite-map view carried by
    `PanStructFiniteState`. All HOL postconditions are included: converted
    evaluation/state, local and global field validity, the global shape map,
    the continuation-local shape map, and the empty result-value obligations.
    The context premise is the HOL fields projection; the state wrapper
    provides finite support without an extra premise. This case stays untagged
    because HOL has a single quantified theorem rather than a named Skip case,
    and Lean represents HOL `(NONE, state)` as a normal clock outcome. -/
theorem panStructCompileCorrectSkipCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (hsourceSkip : panSemEvaluateCodeStateWithPostState evaluationContext
      primitive handler bytesInWord state.runtime (.skip : Prog α) =
        some ((.control (.normal state.runtime.locals state.runtime.globals
          state.runtime.memory state.runtime.ffi), state.runtime.clock), state.runtime))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.skip : Prog α)) =
      some ((.control (.normal
        (panStructConvertFiniteState context state).runtime.locals
        (panStructConvertFiniteState context state).runtime.globals
        (panStructConvertFiniteState context state).runtime.memory
        (panStructConvertFiniteState context state).runtime.ffi),
        (panStructConvertFiniteState context state).runtime.clock),
        (panStructConvertFiniteState context state).runtime) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    panStructShapeMapEq context.locals state.runtime.locals ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have hprojection := panStructFiniteMapSkipEvaluationProjection context
    evaluationContext primitive handler bytesInWord state
  rw [hsourceSkip] at hprojection
  have htarget :
      panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
          bytesInWord (panStructConvertFiniteState context state).runtime
          (structCompileProg context (.skip : Prog α)) =
        some ((.control (.normal
          (panStructConvertFiniteState context state).runtime.locals
          (panStructConvertFiniteState context state).runtime.globals
          (panStructConvertFiniteState context state).runtime.memory
          (panStructConvertFiniteState context state).runtime.ffi),
          (panStructConvertFiniteState context state).runtime.clock),
          (panStructConvertFiniteState context state).runtime) := by
    exact hprojection
  exact ⟨htarget, hlocalsFields, hglobalsFields, hglobalsMap, hlocalsMap,
    by simp [panStructValuesFieldsOkBool], by simp [panIsWfShapeValuesBool]⟩

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

/-- Full Tick specialization of HOL `compile_correct` over finite-map state.
    The evaluator projection handles both HOL branches: timeout clears source
    locals at clock zero, while the continuing branch decrements the clock.
    Every compile_correct postcondition is stated: converted evaluation/state,
    field validity of post locals/globals, global shape-map preservation, the
    continuation-local shape map, and the empty result-value validity/WF
    obligations. The finite-map state wrapper supplies support and lookup
    relations; no target result is assumed. This remains untagged because HOL
    has no separate named Tick case and encodes its result/state pair with
    `TimeOut`/`NONE`, while Lean uses clock outcomes. -/
theorem panStructCompileCorrectTickCase
    [BEq String] [LawfulBEq String] [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : StructPassContext)
    (evaluationContext : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanStructFiniteState α (FfiState σ))
    (_hstructs : panStructContextShapeView context.structs =
      panStructContextShapeView state.runtime.structs)
    (hlocalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.locals)
    (hglobalsFields : panStructEveryValueFieldsOkBool
      state.runtime.structs state.runtime.globals)
    (_hlocalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.locals)
    (_hglobalsShape : panStructEveryValueShapeWfBool
      state.runtime.structs state.runtime.globals)
    (_hstructInfos : structInfosOk state.runtime.structs)
    (hlocalsMap : panStructShapeMapEq context.locals state.runtime.locals)
    (hglobalsMap : panStructShapeMapEq context.globals state.runtime.globals) :
    panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord (panStructConvertFiniteState context state).runtime
        (structCompileProg context (.tick : Prog α)) =
      (panSemEvaluateCodeStateWithPostState evaluationContext primitive handler
        bytesInWord state.runtime (.tick : Prog α)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState context postState)) ∧
    (if state.runtime.clock = 0 then
      panStructEveryValueFieldsOkBool state.runtime.structs
        (fun _ => none : VarName → Option (PanValue α))
     else
      panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.locals) ∧
    panStructEveryValueFieldsOkBool state.runtime.structs state.runtime.globals ∧
    panStructShapeMapEq context.globals state.runtime.globals ∧
    (state.runtime.clock ≠ 0 →
      panStructShapeMapEq context.locals state.runtime.locals) ∧
    panStructValuesFieldsOkBool (α := α) state.runtime.structs [] = true ∧
    panIsWfShapeValuesBool (α := α) state.runtime.structs [] = true := by
  have heval := panStructTickEvaluatorSupport context evaluationContext
    primitive handler bytesInWord state.runtime
  refine ⟨?_, ?_, hglobalsFields, hglobalsMap, ?_, ?_, ?_⟩
  · simpa [panStructConvertFiniteState] using heval
  · by_cases hzero : state.runtime.clock = 0
    · simp [hzero, panStructEveryValueFieldsOkBool]
    · simpa [hzero] using hlocalsFields
  · intro hcontinue
    exact hlocalsMap
  · simp [panStructValuesFieldsOkBool]
  · simp [panIsWfShapeValuesBool]

end Flapjack
