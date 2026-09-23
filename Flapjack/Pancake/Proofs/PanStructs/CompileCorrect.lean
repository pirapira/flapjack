import Flapjack.Pancake.Proofs.PanStructs
import Flapjack.Pancake.Semantics.PanSem

/-!
The first executable case of the HOL `pan_structsProofScript.sml`
`compile_correct` induction. The conversions mirror `convert_v_def`,
`convert_code_def`, and `convert_s_def` over the source-owned Pancake state.
-/

namespace Flapjack

/- HOL `convert_v`: named records become raw records, retaining field order
   while dropping the source field labels. -/
mutual
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

/-- HOL `convert_code` over the finite code map owned by `PanSemState`.
    Parameter shapes are compiled for the resulting code entry; the body is
    compiled with the original parameter shapes in the local context, as in
    the HOL update `ctxt with locals := params`. -/
def panStructConvertCode [BEq String] (context : StructPassContext)
    (code : PanSemCodeMap α) : PanSemCodeMap α :=
  code.map fun (name, (parameters, body, returnShape)) =>
    (name,
      (parameters.map fun (parameter, shape) =>
          (parameter, structCompileShape context.structs shape),
        structCompileProg { context with locals := parameters } body,
        structCompileShape context.structs returnShape))

/-- HOL `convert_s` over the source runtime state. Every runtime field absent
    from the HOL record update is preserved verbatim. -/
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

@[simp] theorem panStructConvertState_code [BEq String]
    (context : StructPassContext) (state : PanSemState α ffi) :
    (panStructConvertState context state).code =
      panStructConvertCode context state.code := rfl

@[simp] theorem panStructCompileSkip_eq_skip [BEq String]
    (context : StructPassContext) :
    structCompileProg context (.skip : Prog α) = .skip := by
  simp [structCompileProg]

/-- Kernel-checked `Skip` branch of HOL `compile_correct`, with the source and
    converted evaluations both running through the finite-code production
    evaluator. This is a branch lemma, not a separately declared HOL theorem,
    so it intentionally has no `@[hol]` tag. -/
theorem panStructCompileCorrectSkipCase
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

end Flapjack
