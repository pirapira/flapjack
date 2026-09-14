import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeProgramRaiseSourceWordRelation
import Flapjack.CrepeSourceWordRecordRaiseCorrectness
import Flapjack.PanValueFfiClockProjection

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

/-! The clocked terminal FFI branch has a direct Pc result lift.  The
    clocked leaf theorem supplies the complete source post-state and event;
    the projection theorem preserves that event while attaching the
    remaining clock, and the existing Pc relation checks the target event
    against the same source-side state relation. -/
theorem panValuePcFinalFfiResultRel_of_clocked_leaf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (clock : Nat) (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α) (targetState : CrepState α)
    (event targetEvent : FfiFinalEvent) (steps : Nat)
    (finalFfi : FfiState σ)
    (hsteps : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord 1 sourceLocals sourceGlobals sourceMemory
      ffi program =
      some (.finalFfi sourceLocals sourceGlobals sourceMemory finalFfi event, steps))
    (hstate : panValueCrepStateRel structs pcContext sourceLocals sourceGlobals
      sourceMemory targetState)
    (hevent : event = targetEvent) :
    evalPanValueFfiClockLeaf context primitive handler structs functions
      baseAddress topAddress bytesInWord clock sourceLocals sourceGlobals
      sourceMemory ffi program =
      some (.control (.finalFfi sourceLocals sourceGlobals sourceMemory finalFfi event),
        clock) ∧
    (evalPanValueFfiClockLeaf context primitive handler structs functions
      baseAddress topAddress bytesInWord clock sourceLocals sourceGlobals
      sourceMemory ffi program).map panValueFfiClockResultProjection =
      some (.finalFfi sourceLocals sourceGlobals sourceMemory finalFfi event clock) ∧
    panValuePcResultRel structs pcContext exceptionRel exceptionCode globalsLookup
      (.finalFfi sourceLocals sourceGlobals sourceMemory event)
      (.finalFfi targetState targetEvent) := by
  have hclock := evalPanValueFfiClockLeaf_finalFfi context primitive handler
    structs functions baseAddress topAddress bytesInWord clock sourceLocals
    sourceGlobals sourceMemory ffi program sourceLocals sourceGlobals sourceMemory
    finalFfi event steps (hsteps := hsteps)
  refine ⟨hclock, ?_, ?_⟩
  · rw [hclock]
    rfl
  · simp [panValuePcResultRel, hstate, hevent]

/-! The zero-clock Tick branch supplies the corresponding Timeout lift.  The
    source correctness equation is used directly, so local clearing and the
    remaining clock are not abstracted away before entering the Pc boundary;
    other clocked evaluator branches remain explicit obligations. -/
theorem panValuePcTimeoutResultRel_of_clocked_tick_zero
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (pcContext : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (targetState : CrepState α)
    (hstate : panValueCrepStateRel structs pcContext (fun _ => none) globals
      memory targetState) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick =
      some (.timeout (fun _ => none) globals memory ffi, 0) ∧
    (evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi 0
      .tick).map panValueFfiClockResultProjection =
      some (.timeout (fun _ => none) globals memory ffi 0) ∧
    panValuePcResultRel structs pcContext exceptionRel exceptionCode globalsLookup
      (.timeout (fun _ => none) globals memory)
      (.timeout targetState) := by
  have hclock := evalPanValueFfiClockProg_tick_zero context primitive handler
    structs functions baseAddress topAddress bytesInWord fuel locals globals memory
    ffi
  refine ⟨hclock, ?_, ?_⟩
  · rw [hclock]
    rfl
  · simp [panValuePcResultRel, hstate]

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

/-! Concrete two-word counterpart of the scalar global payload observation.
    The two flattened words occupy the consecutive compiler-owned global
    slots used by `storeGlobals`; the distinctness premise prevents the
    second update from overwriting slot zero. -/
def crepPcTwoWordGlobalsLookup [OfNat α 0] [Add α]
    (bytesInWord : α) (state : CrepState α) (value : PanValue α) :
    Option (List α) :=
  match value with
  | .rStruct [.word _, .word _] =>
      match state.globals 0, state.globals (0 + bytesInWord) with
      | some left', some right' => some [left', right']
      | _, _ => none
  | _ => none

theorem panValuePcExceptionResultRel_of_raised_two_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (bytesInWord left right : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException
      (.rStruct [.word left, .word right]) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hdistinct : (0 : α) ≠ 0 + bytesInWord) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord) (fun _ => none) sourceMemory
      sourceException (.rStruct [.word left, .word right])
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) }
      targetException := by
  have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
      state.locals := panValueCrepLocalsRel_empty structs context state.locals
  have hraisedState : panValueCrepRaisedStateRel structs context
      sourceGlobals sourceMemory
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) } 0 := by
    refine ⟨hstate.1, hlocals, ?_⟩
    intro address _
    exact congrFun (show panValueWordMemory sourceMemory = state.memory
      from hstate.2.2) address
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException
      (.rStruct [.word left, .word right])
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) }
      targetException 0 := ⟨hraisedState, hexception⟩
  rw [hstate.1] at hcontrol
  apply panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode (crepPcTwoWordGlobalsLookup bytesInWord)
    (fun _ => none) sourceMemory sourceException
    (.rStruct [.word left, .word right])
    { state with globals :=
        (updateMemory (updateMemory state.globals 0 left)
          (0 + bytesInWord) right) }
    targetException 0 hcontrol hcode
  · intro _
    simp [crepPcTwoWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel,
      updateMemory, hdistinct]
  · simp [panValueShape, Shape.shapeSize]

/-! Semantic word-raise lift.  The source and target evaluator equations are
    supplied by the existing fuel-polymorphic Pancake-to-Crep raise theorem;
    this wrapper turns its global spill result into the exact Pc result
    relation used by the compact boundary. -/
theorem panValuePcRaisedWordSemanticLift
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exception : ExceptionId) (exceptionCode value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExpState state baseAddress topAddress compiled =
      some value)
    (hexception : exceptionRel exception (.word value) exceptionCode)
    (hfresh : state.locals (context.maxVar + 1) = none) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression.toExp) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.word value)) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 4) state
      (compileProg context (.raise exception expression.toExp)) =
      some (.raised
        { state with globals := updateMemory state.globals 0 value }
        exceptionCode) ∧
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      (crepPcWordGlobalsLookup (α := α))
      (.raised (fun _ => none) sourceGlobals sourceMemory exception (.word value))
      (.raised { state with globals := updateMemory state.globals 0 value }
        exceptionCode) := by
  obtain ⟨hsourceEval, htargetEval, hspill, _hexception⟩ :=
    compile_full_pan_value_raise_source_word_global_relation_fuel
      context structs sourceFunctions functions sourceLocals sourceGlobals
      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord sourceFuel targetFuel exception
      exceptionCode value expression compiled exceptionRel hlookup
      hbytesInWord hrel hsource hcompile hcompiled hexception hfresh
  have hstateEmpty : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory state := by
    refine ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
    exact hrel.2.2
  have hexceptionResult := panValuePcExceptionResultRel_of_raised_word_global_spill
    structs context exceptionRel resultExceptionCode sourceGlobals sourceMemory
    exception value state exceptionCode hstateEmpty hexception hcode
  have hpost : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { state with globals := updateMemory state.globals 0 value } := by
    refine ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
    exact hrel.2.2
  have hexceptionResult' :
      panValuePcExceptionResultRel structs context exceptionRel resultExceptionCode
        (crepPcWordGlobalsLookup (α := α)) sourceGlobals sourceMemory
        exception (.word value)
        { state with globals := updateMemory state.globals 0 value }
        exceptionCode := by
    simpa [hrel.1] using hexceptionResult
  exact ⟨hsourceEval, htargetEval, ⟨hpost, hexceptionResult'⟩⟩

/-! Adapter for the generic `pc_compile_correct` raised obligation.  The
    existing word semantic lift supplies the concrete evaluator equations;
    this theorem exposes its result component in the exact explicit shape
    consumed by `panValuePcCompileCorrect_compact`, including the source
    exception lookup, post-state relation, global payload observation, and
    32-word bound. -/
theorem panValuePcRaisedWordHraise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exception : ExceptionId) (exceptionCode value : α)
    (expression : SourceWordExp α) (compiled : CrepExp α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression.toExp = some (.word value))
    (hcompile : compileExp context expression.toExp = ([compiled], .one))
    (hcompiled : evalCrepFullExpState state baseAddress topAddress compiled =
      some value)
    (hexception : exceptionRel exception (.word value) exceptionCode)
    (hfresh : state.locals (context.maxVar + 1) = none) :
    panValueCrepStateRel structs context (fun _ => none) sourceGlobals
      sourceMemory { state with globals := updateMemory state.globals 0 value } ∧
    (∃ spillAddress,
      panValueCrepRaisedControlRel structs context exceptionRel sourceGlobals
        sourceMemory exception (.word value)
        { state with globals := updateMemory state.globals 0 value }
        exceptionCode spillAddress ∧
      resultExceptionCode exception = some exceptionCode ∧
      (1 ≤ Shape.shapeSize (panValueShape structs (.word value)) →
        crepPcWordGlobalsLookup
          { state with globals := updateMemory state.globals 0 value }
          (.word value) = some (panValueFlatWords (.word value))) ∧
      Shape.shapeSize (panValueShape structs (.word value)) ≤ 32) := by
  have hresult := panValuePcRaisedWordSemanticLift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exception
    exceptionCode value expression compiled exceptionRel resultExceptionCode
    hlookup hcode hbytesInWord hrel hsource hcompile hcompiled hexception hfresh
  rcases hresult.2.2 with
    ⟨hpost, spillAddress, code, hresultCode, htargetCode, hcontrol, hpayload⟩
  refine ⟨hpost, spillAddress, hcontrol, ?_, ?_, ?_⟩
  · simpa [htargetCode] using hresultCode
  · intro hnonempty
    exact (hpayload hnonempty).1
  · simp [panValueShape]

/-! Semantic two-word raise lift for the next supported payload fragment.  The
    source and global-aware Crep equations are the checked two-word
    `CrepeCorrectness` boundary; the result clause retains both global words
    and its non-aliasing condition.  Clocked `TimeOut` and terminal `FinalFFI`
    remain outside this compact evaluator fragment. -/
theorem panValuePcRaisedTwoWordSemanticLift
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (fieldLeft fieldRight : SourceWordExp α) (left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (compiledLeft compiledRight : CrepExp α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hdistinct : (0 : α) ≠ 0 + bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      some (.rStruct [.word left, .word right]))
    (hcompile : compileExp context
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      ([compiledLeft, compiledRight], .comb [.one, .one]))
    (hcompiledLeft : evalCrepFullExpState state baseAddress topAddress compiledLeft =
      some left)
    (hcompiledRight : ∀ value : α, evalCrepFullExpState
      { state with locals := updateCrepLocal state.locals (context.maxVar + 1) value }
      baseAddress topAddress compiledRight = some right)
    (hexception : exceptionRel exception
      (.rStruct [.word left, .word right]) exceptionCode) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord 5
      sourceLocals sourceGlobals sourceMemory
      (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp])) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct [.word left, .word right])) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress 15 state
      (compileProg context
        (.raise exception (.rStruct [fieldLeft.toExp, fieldRight.toExp]))) =
      some (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode) ∧
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord)
      (.raised (fun _ => none) sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right]))
      (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode) := by
  obtain ⟨hsourceEval, htargetEval, _hraiseData⟩ :=
    compile_full_pan_value_raise_source_word_two_fields_state_relation
      context structs sourceFunctions functions sourceLocals sourceGlobals
      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord fieldLeft fieldRight left right
      exception exceptionCode exceptionRel compiledLeft compiledRight hlookup
      hbytesInWord hrel hsource hcompile hcompiledLeft hcompiledRight hexception
  have hstateEmpty : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory state := by
    refine ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
    exact hrel.2.2
  have hexceptionResult :=
    panValuePcExceptionResultRel_of_raised_two_word_global_spill
      structs context exceptionRel resultExceptionCode sourceGlobals sourceMemory
      exception bytesInWord left right state exceptionCode hstateEmpty hexception
      hcode hdistinct
  have hpost : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) } := by
    refine ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
    exact hrel.2.2
  have hexceptionResult' :
      panValuePcExceptionResultRel structs context exceptionRel resultExceptionCode
        (crepPcTwoWordGlobalsLookup bytesInWord) sourceGlobals sourceMemory
        exception (.rStruct [.word left, .word right])
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode := by
    simpa [hrel.1] using hexceptionResult
  exact ⟨hsourceEval, htargetEval, ⟨hpost, hexceptionResult'⟩⟩

/-! The two-word counterpart exposes the existing structured-payload semantic
    lift in the explicit generic `hraise` shape.  The distinct spill slots and
    the two-word global observer remain part of the obligation. -/
theorem panValuePcRaisedTwoWordHraise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (fieldLeft fieldRight : SourceWordExp α) (left right : α)
    (exception : ExceptionId) (exceptionCode : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (compiledLeft compiledRight : CrepExp α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hdistinct : (0 : α) ≠ 0 + bytesInWord)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      some (.rStruct [.word left, .word right]))
    (hcompile : compileExp context
      (.rStruct [fieldLeft.toExp, fieldRight.toExp]) =
      ([compiledLeft, compiledRight], .comb [.one, .one]))
    (hcompiledLeft : evalCrepFullExpState state baseAddress topAddress compiledLeft =
      some left)
    (hcompiledRight : ∀ value : α, evalCrepFullExpState
      { state with locals := updateCrepLocal state.locals (context.maxVar + 1) value }
      baseAddress topAddress compiledRight = some right)
    (hexception : exceptionRel exception
      (.rStruct [.word left, .word right]) exceptionCode) :
    panValueCrepStateRel structs context (fun _ => none) sourceGlobals
      sourceMemory
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) } ∧
    (∃ spillAddress,
      panValueCrepRaisedControlRel structs context exceptionRel sourceGlobals
        sourceMemory exception (.rStruct [.word left, .word right])
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode spillAddress ∧
      resultExceptionCode exception = some exceptionCode ∧
      (1 ≤ Shape.shapeSize
          (panValueShape structs (.rStruct [.word left, .word right])) →
        crepPcTwoWordGlobalsLookup bytesInWord
            { state with globals :=
                (updateMemory (updateMemory state.globals 0 left)
                  (0 + bytesInWord) right) }
            (.rStruct [.word left, .word right]) =
          some (panValueFlatWords (.rStruct [.word left, .word right]))) ∧
      Shape.shapeSize (panValueShape structs
        (.rStruct [.word left, .word right])) ≤ 32) := by
  have hresult := panValuePcRaisedTwoWordSemanticLift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fieldLeft fieldRight
    left right exception exceptionCode exceptionRel resultExceptionCode
    compiledLeft compiledRight hlookup hcode hbytesInWord hdistinct hrel hsource
    hcompile hcompiledLeft hcompiledRight hexception
  rcases hresult.2.2 with
    ⟨hpost, spillAddress, code, hresultCode, htargetCode, hcontrol, hpayload⟩
  have hnonempty : 1 ≤ Shape.shapeSize
      (panValueShape structs (.rStruct [.word left, .word right])) := by
    simp [panValueShape, Shape.shapeSize]
  have hshape : Shape.shapeSize
      (panValueShape structs (.rStruct [.word left, .word right])) ≤ 32 := by
    simp [panValueShape, Shape.shapeSize]
  refine ⟨hpost, spillAddress, hcontrol, ?_, ?_, ?_⟩
  · simpa [htargetCode] using hresultCode
  · intro _
    exact (hpayload hnonempty).1
  · exact hshape

/-! The explicit raised-result package consumed by the compact top-level
    theorem. -/
def panValuePcRaisedHraiseData
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) : Prop :=
  panValueCrepStateRel structs context sourceLocals sourceGlobals
    sourceMemory targetState ∧
  (∃ spillAddress,
    panValueCrepRaisedControlRel structs context exceptionRel sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException
      spillAddress ∧
    exceptionCode sourceException = some targetException ∧
    (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue =
        some (panValueFlatWords sourceValue)) ∧
    Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)

/-! Dispatch the supported raised payload cases into the universal `hraise`
    slot consumed by `panValuePcCompileCorrect_compact`.  The word and exact
    two-word callbacks are the semantic adapters above; the fallback is
    deliberately restricted to payloads outside those cases, so this bridge
    does not hide an unsupported raise or a clocked `Timeout`/`FinalFFI`. -/
theorem panValuePcRaisedHraiseCases
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hword : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (value : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.word value) targetState targetException)
    (htwo : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (left right : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word left, .word right]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word left, .word right]) targetState targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ left right : α,
        sourceValue ≠ .rStruct [.word left, .word right]) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException) :
    ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  cases sourceValue with
  | word value =>
      exact hword context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException value targetState targetException hcontrol
  | rStruct fields =>
      cases fields with
      | nil =>
          exact hother context structs exceptionRel sourceLocals sourceGlobals
            sourceMemory sourceException (.rStruct []) targetState targetException
            (by simp) (by simp) hcontrol
      | cons first rest =>
          cases first with
          | word left =>
              cases rest with
              | nil =>
                  exact hother context structs exceptionRel sourceLocals sourceGlobals
                    sourceMemory sourceException (.rStruct [.word left]) targetState
                    targetException (by simp) (by simp) hcontrol
              | cons second tail =>
                  cases second with
                  | word right =>
                      cases tail with
                      | nil =>
                          exact htwo context structs exceptionRel sourceLocals
                            sourceGlobals sourceMemory sourceException left right
                            targetState targetException hcontrol
                      | cons third tail' =>
                          exact hother context structs exceptionRel sourceLocals
                            sourceGlobals sourceMemory sourceException
                            (.rStruct (.word left :: .word right :: third :: tail'))
                            targetState targetException (by simp) (by simp) hcontrol
                  | rStruct fields =>
                      exact hother context structs exceptionRel sourceLocals
                        sourceGlobals sourceMemory sourceException
                        (.rStruct (.word left :: .rStruct fields :: tail))
                        targetState targetException (by simp) (by simp) hcontrol
                  | nStruct name fields =>
                      exact hother context structs exceptionRel sourceLocals
                        sourceGlobals sourceMemory sourceException
                        (.rStruct (.word left :: .nStruct name fields :: tail))
                        targetState targetException (by simp) (by simp) hcontrol
          | rStruct fields =>
              exact hother context structs exceptionRel sourceLocals sourceGlobals
                sourceMemory sourceException
                (.rStruct (.rStruct fields :: rest)) targetState targetException
                (by simp) (by simp) hcontrol
          | nStruct name fields =>
              exact hother context structs exceptionRel sourceLocals sourceGlobals
                sourceMemory sourceException
                (.rStruct (.nStruct name fields :: rest)) targetState targetException
                (by simp) (by simp) hcontrol
  | nStruct name fields =>
      exact hother context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException (.nStruct name fields) targetState targetException
        (by simp) (by simp) hcontrol

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
    (hword : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (value : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.word value) targetState targetException)
    (htwo : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (left right : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word left, .word right]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word left, .word right]) targetState targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ left right : α,
        sourceValue ≠ .rStruct [.word left, .word right]) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraise := panValuePcRaisedHraiseCases exceptionCode globalsLookup
    hword htwo hother
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
