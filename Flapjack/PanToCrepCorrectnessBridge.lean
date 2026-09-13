import Flapjack.PanToCrepCorrectnessBoundary

/-!
Bridge from the existing stateful source-to-Crep program correctness contract
to the exact `pc_compile_correct` boundary.  This theorem is intentionally
adapter-parametric: the stateful evaluator already proves the five compact
control cases, while the adapters and result lift must account for the
clocked `TimeOut` and `FinalFFI` cases before a concrete top-level evaluator
can instantiate the full boundary.
-/

namespace Flapjack

def panValuePcResultOfControl :
    PanValueControlResult α → PanValuePcResult α
  | .normal locals globals memory => .normal locals globals memory
  | .returned locals globals memory values =>
      .returned locals globals memory values
  | .raised locals globals memory exception value =>
      .raised locals globals memory exception value
  | .broke locals globals memory => .broke locals globals memory
  | .continued locals globals memory => .continued locals globals memory

def crepPcResultOfControl :
    CrepControlResult α → Option (CrepPcResult α)
  | .normal state => some (.normal state)
  | .returned state values => some (.returned state values)
  | .raised state exception => some (.raised state exception)
  | .broke state label => some (.broke state label)
  | .continued state label => some (.continued state label)
  | .finalFfi _ _ => none

def panValuePcCompactSourceEvaluator
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat) :
    PanValuePcEvaluator α :=
  fun _ input program =>
    (evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler input.structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      input.locals input.globals input.memory program).map
      (fun result =>
        { code := input.code
          , eshapes := input.eshapes
          , result := panValuePcResultOfControl result })

def crepPcCompactTargetEvaluator
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat) :
    CrepPcEvaluator α :=
  fun _ input program =>
    (evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel input.state program).bind
      (fun result =>
        (crepPcResultOfControl result).map
          (fun targetResult =>
            { code := input.code
              , eshapes := input.eshapes
              , result := targetResult }))

theorem panValuePcCompactSourceEvaluator_adapter
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (program : Prog α)
    (context : CompileContext α) (structs : StructContext)
    (sourceInput : PanValuePcInput α) (_targetInput : CrepPcInput α)
    (sourceExecution : PanValuePcExecution α)
    (hstructs : sourceInput.structs = structs)
    (heval : panValuePcCompactSourceEvaluator primitive sourceHandler
        sourceFunctions baseAddress topAddress bytesInWord sourceFuel
        context sourceInput program = some sourceExecution) :
    ∃ sourceResult,
      evalPanValueProgWithPrimitiveCallsAndFfi
        primitive sourceHandler structs sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel
        sourceInput.locals sourceInput.globals sourceInput.memory program =
          some sourceResult ∧
      sourceExecution.result = panValuePcResultOfControl sourceResult := by
  cases hsource : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler sourceInput.structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceInput.locals sourceInput.globals sourceInput.memory program with
  | none => simp [panValuePcCompactSourceEvaluator, hsource] at heval
  | some sourceResult =>
      refine ⟨sourceResult, ?_, ?_⟩
      · simpa [hstructs] using hsource
      · have heval' :
            ({ code := sourceInput.code
                , eshapes := sourceInput.eshapes
                , result := panValuePcResultOfControl sourceResult } :
              PanValuePcExecution α) = sourceExecution := by
          simpa [panValuePcCompactSourceEvaluator, hsource] using heval
        exact (congrArg (fun execution : PanValuePcExecution α => execution.result)
          heval').symm

theorem crepPcCompactTargetEvaluator_adapter
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat)
    (program : Prog α)
    (context : CompileContext α) (structs : StructContext)
    (_sourceInput : PanValuePcInput α) (targetInput : CrepPcInput α)
    (targetExecution : CrepPcExecution α)
    (_hstructs : targetInput.structs = structs)
    (heval : crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel context targetInput
        (compileProg context program) = some targetExecution) :
    ∃ crepResult,
      evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel targetInput.state
        (compileProg context program) = some crepResult ∧
      crepPcResultOfControl crepResult = some targetExecution.result := by
  cases htarget : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel targetInput.state
      (compileProg context program) with
  | none => simp [crepPcCompactTargetEvaluator, htarget] at heval
  | some crepResult =>
      cases hmap : crepPcResultOfControl crepResult with
      | none => simp [crepPcCompactTargetEvaluator, htarget, hmap] at heval
      | some targetResult =>
          refine ⟨crepResult, ?_, ?_⟩
          · rfl
          have heval' :
              ({ code := targetInput.code
                , eshapes := targetInput.eshapes
                , result := targetResult } : CrepPcExecution α) = targetExecution := by
            simpa [crepPcCompactTargetEvaluator, htarget, hmap] using heval
          simpa [hmap] using
            congrArg (fun execution : CrepPcExecution α => some execution.result)
              heval'

/-! The HOL exception branch first turns the existing raised control relation
    into the exact exception-code/payload result clause.  The lookup,
    observation, and 32-word premises stay explicit, matching the source
    theorem rather than hiding them in a weaker compatibility predicate. -/
theorem panValuePcExceptionResultRel_of_raised_control
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (sourceValue : PanValue α)
    (targetState : CrepState α) (targetException spillAddress : α)
    (hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException spillAddress)
    (hcode : exceptionCode sourceException = some targetException)
    (hlookup : 1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      globalsLookup sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException := by
  refine ⟨spillAddress, targetException, hcode, rfl, hcontrol, ?_⟩
  intro hnonempty
  exact ⟨hlookup hnonempty, hsize⟩

/-! Concrete one-word instance of the HOL `globals_lookup` observation.  The
    global-aware raise relation already proves that address zero contains the
    flattened payload; this theorem supplies the exact Pc exception clause,
    including its lower-bound guard and 32-word upper bound. -/
def crepPcWordGlobalsLookup [OfNat α 0]
    (state : CrepState α) (value : PanValue α) :
    Option (List α) :=
  match value with
  | .word _ => (state.globals 0).map (fun stored => [stored])
  | _ => none

theorem panValuePcExceptionResultRel_of_raised_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (value : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException (.word value) targetException)
    (hcode : exceptionCode sourceException = some targetException) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      (crepPcWordGlobalsLookup (α := α)) (fun _ => none) sourceMemory
      sourceException (.word value)
      { state with globals := updateMemory state.globals 0 value }
      targetException := by
  have hraised := panValueCrepRaisedGlobalSpillRel_word
    structs context (fun _ => none) sourceGlobals sourceMemory state 0 value hstate
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException (.word value)
      { state with globals := updateMemory state.globals 0 value }
      targetException 0 := ⟨hraised.1, hexception⟩
  rw [hstate.1] at hcontrol
  apply panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode (crepPcWordGlobalsLookup (α := α))
    (fun _ => none) sourceMemory sourceException (.word value)
    { state with globals := updateMemory state.globals 0 value }
    targetException 0 hcontrol hcode
  · intro _
    simp [crepPcWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, updateMemory]
  · simp [panValueShape]

/-! The ordinary compact control cases are proved directly from the existing
`panValueCrepControlRel`.  Only the raised payload needs an additional
obligation because the exact Pc relation retains both the HOL post-state
relation and the exception-code/global-payload clause. -/
theorem panValuePcResultRel_of_control
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hraise : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (targetResult : CrepPcResult α)
    (hcontrol : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult)
    (hresult : crepPcResultOfControl crepResult = some targetResult) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (panValuePcResultOfControl sourceResult) targetResult := by
  cases sourceResult with
  | normal sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | normal targetState =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | returned _ _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | returned sourceLocals sourceGlobals sourceMemory sourceValues =>
      cases crepResult with
      | returned targetState targetValues =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue =>
      cases crepResult with
      | raised targetState targetException =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using
            (hraise sourceLocals sourceGlobals sourceMemory sourceException
              sourceValue targetState targetException hcontrol)
      | normal _ | returned _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | broke sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | broke targetState targetLabel =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | continued sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | continued targetState targetLabel =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | broke _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol

/-! A kernel-checked composition theorem for the stateful source-to-Crep
proof.  `hsourceAdapter` and `htargetAdapter` identify the rich evaluator's
successful result with the existing stateful evaluators.  Ordinary
normal/return/break/continue results are then proved by
`panValuePcResultRel_of_control`; only the raised payload/state clause is an
explicit obligation.  Because the target compact evaluator has no timeout
case, the theorem does not silently claim the missing clocked/FinalFFI proof.
-/
theorem panValuePcCompileCorrect_of_stateful_program
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (sourceEvaluate : PanValuePcEvaluator α)
    (targetEvaluate : CrepPcEvaluator α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (hprogram : PanValueCrepProgramStateCorrect program)
    (hsourceAdapter : ∀ (context : CompileContext α)
      (structs : StructContext) (sourceInput : PanValuePcInput α)
      (_targetInput : CrepPcInput α)
      (sourceExecution : PanValuePcExecution α),
      sourceInput.structs = structs →
      sourceEvaluate context sourceInput program = some sourceExecution →
      ∃ sourceResult,
        evalPanValueProgWithPrimitiveCallsAndFfi
          primitive sourceHandler structs sourceFunctions
          baseAddress topAddress bytesInWord sourceFuel
          sourceInput.locals sourceInput.globals sourceInput.memory program =
            some sourceResult ∧
        sourceExecution.result = panValuePcResultOfControl sourceResult)
    (htargetAdapter : ∀ (context : CompileContext α)
      (structs : StructContext) (_sourceInput : PanValuePcInput α)
      (targetInput : CrepPcInput α) (targetExecution : CrepPcExecution α),
      targetInput.structs = structs →
      targetEvaluate context targetInput (compileProg context program) =
        some targetExecution →
      ∃ crepResult,
        evalCrepFullProgState functions crepPrimitive ffi sharedMem
          baseAddress topAddress targetFuel targetInput.state
          (compileProg context program) = some crepResult ∧
        crepPcResultOfControl crepResult = some targetExecution.result)
    (hraise : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hdistinct hlocalisedCode
    hlocalised hcode hexcp hstate hnonerror hsource htarget hpostCode hpostExcp
  obtain ⟨sourceResult, hsourceResult, hsourceShape⟩ :=
    hsourceAdapter context structs sourceInput targetInput sourceExecution
      hsourceStructs hsource
  obtain ⟨crepResult, hcrepResult, hcrepShape⟩ :=
    htargetAdapter context structs sourceInput targetInput targetExecution
      htargetStructs htarget
  have hcontrol := hprogram context structs sourceFunctions functions
    sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
    hstate hsourceResult hcrepResult
  have hresult := panValuePcResultRel_of_control structs context exceptionRel
    exceptionCode globalsLookup (hraise context structs exceptionRel)
    sourceResult crepResult targetExecution.result hcontrol hcrepShape
  simpa [hsourceShape] using hresult

/-! Concrete instantiation for the currently supported compact evaluator
fragment.  This packages both evaluator adapters into the stateful bridge;
raised payload/global compatibility and the clocked `TimeOut`/`FinalFFI`
cases remain explicit hypotheses rather than being erased by the adapter. -/
theorem panValuePcCompileCorrect_compact
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α)
    (codeRel : PanValuePcCodeRel α)
    (excpRel : PanValuePcExceptionShapeRel α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (hprogram : PanValueCrepProgramStateCorrect program)
    (hraise : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      (∃ spillAddress,
        panValueCrepRaisedControlRel structs context exceptionRel
          sourceGlobals sourceMemory sourceException sourceValue targetState
          targetException spillAddress ∧
        exceptionCode sourceException = some targetException ∧
        (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
          globalsLookup targetState sourceValue =
            some (panValueFlatWords sourceValue)) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraise' : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException := by
    intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException hcontrol
    obtain ⟨hpost, hraiseData⟩ :=
      hraise context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
    obtain ⟨spillAddress, hraised, hcode, hlookup, hsize⟩ := hraiseData
    refine ⟨hpost, ?_⟩
    exact panValuePcExceptionResultRel_of_raised_control structs context
      exceptionRel exceptionCode globalsLookup sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException spillAddress
      hraised hcode hlookup hsize
  refine panValuePcCompileCorrect_of_stateful_program
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram ?_ ?_ hraise'
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval

end Flapjack
