import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeProgramGenericRaiseCorrectness
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

/-! Cake-faithful raised-result constructor.  In addition to the existing
    spill/code/payload obligations, the source exception must resolve through
    the compiler context, exactly as `FLOOKUP ctxt.eids eid` does in HOL. -/
theorem panValuePcExceptionResultRelWithContextCode_of_raised_control
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
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException)
    (hlookup : 1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException := by
  refine ⟨?_, hlookupCode⟩
  exact panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode globalsLookup sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException spillAddress hcontrol
    hcode hlookup hsize

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
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (value : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException (.word value) targetException)
    (hcode : exceptionCode sourceException = some targetException) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      (crepPcWordGlobalsLookup (α := α)) sourceGlobals sourceMemory
      sourceException (.word value)
      { state with globals := updateMemory state.globals 0 value }
      targetException := by
  have hraised := panValueCrepRaisedGlobalSpillRel_word
    structs context sourceLocals sourceGlobals sourceMemory state 0 value hstate
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException (.word value)
      { state with globals := updateMemory state.globals 0 value }
      targetException 0 := ⟨hraised.1, hexception⟩
  apply panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode (crepPcWordGlobalsLookup (α := α))
    sourceGlobals sourceMemory sourceException (.word value)
    { state with globals := updateMemory state.globals 0 value }
    targetException 0 hcontrol hcode
  · intro _
    simp [crepPcWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, updateMemory]
  · simp [panValueShape]

theorem panValuePcResultRelWithContextCode_of_raised_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (value : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException (.word value) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      (crepPcWordGlobalsLookup (α := α))
      (.raised sourceLocals sourceGlobals sourceMemory sourceException (.word value))
      (.raised
        { state with globals := updateMemory state.globals 0 value }
        targetException) := by
  have hpost : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory
      { state with globals := updateMemory state.globals 0 value } := by
    exact ⟨hstate.1, hstate.2.1, hstate.2.2⟩
  have hresult := panValuePcExceptionResultRel_of_raised_word_global_spill
    structs context exceptionRel exceptionCode sourceLocals sourceGlobals
    sourceMemory sourceException value state targetException hstate hexception hcode
  refine ⟨hpost, ?_⟩
  exact ⟨hresult, hlookupCode⟩

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
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (bytesInWord left right : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException
      (.rStruct [.word left, .word right]) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hdistinct : (0 : α) ≠ 0 + bytesInWord) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord) sourceGlobals sourceMemory
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
  apply panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode (crepPcTwoWordGlobalsLookup bytesInWord)
    sourceGlobals sourceMemory sourceException
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

theorem panValuePcResultRelWithContextCode_of_raised_two_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (bytesInWord left right : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException
      (.rStruct [.word left, .word right]) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException)
    (hdistinct : (0 : α) ≠ 0 + bytesInWord) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word left, .word right]))
      (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        targetException) := by
  have hpost : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory
      { state with globals :=
          (updateMemory (updateMemory state.globals 0 left)
            (0 + bytesInWord) right) } := by
    exact ⟨hstate.1, hstate.2.1, hstate.2.2⟩
  refine ⟨hpost, ?_⟩
  refine ⟨?_, hlookupCode⟩
  simpa [hstate.1] using
    (panValuePcExceptionResultRel_of_raised_two_word_global_spill
      structs context exceptionRel exceptionCode sourceLocals sourceGlobals
      sourceMemory
      sourceException bytesInWord left right state targetException hstate
      hexception hcode hdistinct)

def crepPcThreeWordGlobalsLookup [OfNat α 0] [Add α]
    (bytesInWord : α) (state : CrepState α) (value : PanValue α) :
    Option (List α) :=
  match value with
  | .rStruct [.word _, .word _, .word _] =>
      match state.globals 0, state.globals (0 + bytesInWord),
        state.globals ((0 + bytesInWord) + bytesInWord) with
      | some first, some second, some third => some [first, second, third]
      | _, _, _ => none
  | _ => none

theorem panValuePcExceptionResultRel_of_raised_three_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (bytesInWord first second third : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException
      (.rStruct [.word first, .word second, .word third]) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hdistinct01 : (0 : α) ≠ 0 + bytesInWord)
    (hdistinct02 : (0 : α) ≠ (0 + bytesInWord) + bytesInWord)
    (hdistinct12 : (0 : α) + bytesInWord ≠
      (0 + bytesInWord) + bytesInWord) :
    panValuePcExceptionResultRel structs context exceptionRel exceptionCode
      (crepPcThreeWordGlobalsLookup bytesInWord) sourceGlobals sourceMemory
      sourceException (.rStruct [.word first, .word second, .word third])
      { state with globals :=
          (updateMemoryListAt state.globals 0 bytesInWord
            [first, second, third]) }
      targetException := by
  have hlocals : panValueCrepLocalsRel structs context (fun _ => none)
      state.locals := panValueCrepLocalsRel_empty structs context state.locals
  have hraisedState : panValueCrepRaisedStateRel structs context
      sourceGlobals sourceMemory
      { state with globals :=
          (updateMemoryListAt state.globals 0 bytesInWord
            [first, second, third]) } 0 := by
    refine ⟨hstate.1, hlocals, ?_⟩
    intro address _
    exact congrFun (show panValueWordMemory sourceMemory = state.memory
      from hstate.2.2) address
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException
      (.rStruct [.word first, .word second, .word third])
      { state with globals :=
          (updateMemoryListAt state.globals 0 bytesInWord
            [first, second, third]) }
      targetException 0 := ⟨hraisedState, hexception⟩
  apply panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode (crepPcThreeWordGlobalsLookup bytesInWord)
    sourceGlobals sourceMemory sourceException
    (.rStruct [.word first, .word second, .word third])
    { state with globals :=
        (updateMemoryListAt state.globals 0 bytesInWord
          [first, second, third]) }
    targetException 0 hcontrol hcode
  · intro _
    simp [crepPcThreeWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel,
      updateMemoryListAt, updateMemory, hdistinct01, hdistinct02,
      hdistinct12]
  · simp [panValueShape, Shape.shapeSize]

theorem panValuePcResultRelWithContextCode_of_raised_three_word_global_spill
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId)
    (bytesInWord first second third : α)
    (state : CrepState α) (targetException : α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException
      (.rStruct [.word first, .word second, .word third]) targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException)
    (hdistinct01 : (0 : α) ≠ 0 + bytesInWord)
    (hdistinct02 : (0 : α) ≠ (0 + bytesInWord) + bytesInWord)
    (hdistinct12 : (0 : α) + bytesInWord ≠
      (0 + bytesInWord) + bytesInWord) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      (crepPcThreeWordGlobalsLookup bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]))
      (.raised
        { state with globals :=
            (updateMemoryListAt state.globals 0 bytesInWord
              [first, second, third]) }
        targetException) := by
  have hpost : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory
      { state with globals :=
          (updateMemoryListAt state.globals 0 bytesInWord
            [first, second, third]) } := by
    exact ⟨hstate.1, hstate.2.1, hstate.2.2⟩
  refine ⟨hpost, ?_⟩
  refine ⟨?_, hlookupCode⟩
  simpa [hstate.1] using
    (panValuePcExceptionResultRel_of_raised_three_word_global_spill
      structs context exceptionRel exceptionCode sourceLocals sourceGlobals sourceMemory
      sourceException bytesInWord first second third state targetException hstate
      hexception hcode hdistinct01 hdistinct02 hdistinct12)

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
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
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
    structs context exceptionRel resultExceptionCode (fun _ => none) sourceGlobals
    sourceMemory
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
  have hcontext : panValuePcResultRelWithContextCode structs context
      exceptionRel resultExceptionCode
      (crepPcWordGlobalsLookup (α := α))
      (.raised (fun _ => none) sourceGlobals sourceMemory exception (.word value))
      (.raised { state with globals := updateMemory state.globals 0 value }
        exceptionCode) := by
    simpa [panValuePcResultRelWithContextCode] using
      (show panValueCrepStateRel structs context
          (fun _ => none) sourceGlobals sourceMemory
          { state with globals := updateMemory state.globals 0 value } ∧
        panValuePcExceptionResultRelWithContextCode structs context exceptionRel
          resultExceptionCode (crepPcWordGlobalsLookup (α := α))
          sourceGlobals sourceMemory exception (.word value)
          { state with globals := updateMemory state.globals 0 value }
          exceptionCode from
        ⟨hpost, ⟨hexceptionResult', hlookup⟩⟩)
  exact ⟨hsourceEval, htargetEval, hcontext⟩

/-! Focused result-relation instantiation of the checked word semantic lift.
    Callers that already have the source/target raise premises can consume
    the exact Pc result relation without unpacking the evaluator equations. -/
theorem panValuePcRaisedWordResultRel_of_semantic_lift
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
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
      (crepPcWordGlobalsLookup (α := α))
      (.raised (fun _ => none) sourceGlobals sourceMemory exception (.word value))
      (.raised { state with globals := updateMemory state.globals 0 value }
        exceptionCode) := by
  have hresult := panValuePcRaisedWordSemanticLift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exception
    exceptionCode value expression compiled exceptionRel resultExceptionCode
    hlookup hcode hbytesInWord hrel hsource hcompile hcompiled hexception hfresh
  exact hresult.2.2

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
    (panValueCrepStateRel structs context (fun _ => none) sourceGlobals
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
        Shape.shapeSize (panValueShape structs (.word value)) ≤ 32)) ∧
    lookupInfo exception context.exceptions = some exceptionCode := by
  have hresult := panValuePcRaisedWordResultRel_of_semantic_lift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exception
    exceptionCode value expression compiled exceptionRel resultExceptionCode
    hlookup hcode hbytesInWord hrel hsource hcompile hcompiled hexception hfresh
  rcases hresult with ⟨hpost, hcontext⟩
  rcases hcontext with ⟨hordinary, hlookupCode⟩
  rcases hordinary with
    ⟨spillAddress, code, hresultCode, htargetCode, hcontrol, hpayload⟩
  refine ⟨?_, hlookupCode⟩
  refine ⟨hpost, ?_⟩
  refine ⟨spillAddress, hcontrol, ?_, ?_, ?_⟩
  · simpa [htargetCode] using hresultCode
  · intro hnonempty
    exact (hpayload hnonempty).1
  · simp [panValueShape]

theorem panValuePcRaisedWordResultRel_retarget_globals
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
    (globalsLookup : CrepState α → PanValue α → Option (List α))
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
    (hfresh : state.locals (context.maxVar + 1) = none)
    (hlookupGlobals : crepPcWordGlobalsLookup
        { state with globals := updateMemory state.globals 0 value }
        (.word value) = globalsLookup
          { state with globals := updateMemory state.globals 0 value }
          (.word value)) :
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
      globalsLookup
      (.raised (fun _ => none) sourceGlobals sourceMemory exception (.word value))
      (.raised { state with globals := updateMemory state.globals 0 value }
        exceptionCode) := by
  have hword := panValuePcRaisedWordHraise
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exception
    exceptionCode value expression compiled exceptionRel resultExceptionCode
    hlookup hcode hbytesInWord hrel hsource hcompile hcompiled hexception hfresh
  rcases hword with ⟨hwordData, hlookupCode⟩
  rcases hwordData with
    ⟨hpost, spillAddress, hcontrol, hcode', hpayload, hsize⟩
  refine ⟨hpost, ?_⟩
  refine ⟨?_, hlookupCode⟩
  apply panValuePcExceptionResultRel_of_raised_control
    structs context exceptionRel resultExceptionCode globalsLookup
    sourceGlobals sourceMemory exception (.word value)
    { state with globals := updateMemory state.globals 0 value }
    exceptionCode spillAddress hcontrol hcode'
  intro hnonempty
  rw [← hlookupGlobals]
  exact hpayload hnonempty
  exact hsize

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
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
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
      structs context exceptionRel resultExceptionCode (fun _ => none) sourceGlobals
      sourceMemory
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
  have hcontext : panValuePcResultRelWithContextCode structs context
      exceptionRel resultExceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord)
      (.raised (fun _ => none) sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right]))
      (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode) := by
    simpa [panValuePcResultRelWithContextCode] using
      (show panValueCrepStateRel structs context
          (fun _ => none) sourceGlobals sourceMemory
          { state with globals :=
              (updateMemory (updateMemory state.globals 0 left)
                (0 + bytesInWord) right) } ∧
        panValuePcExceptionResultRelWithContextCode structs context
          exceptionRel resultExceptionCode
          (crepPcTwoWordGlobalsLookup bytesInWord)
          sourceGlobals sourceMemory exception
          (.rStruct [.word left, .word right])
          { state with globals :=
              (updateMemory (updateMemory state.globals 0 left)
                (0 + bytesInWord) right) }
          exceptionCode from
        ⟨hpost, ⟨hexceptionResult', hlookup⟩⟩)
  exact ⟨hsourceEval, htargetEval, hcontext⟩

theorem panValuePcRaisedTwoWordResultRel_of_semantic_lift
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
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      (crepPcTwoWordGlobalsLookup bytesInWord)
      (.raised (fun _ => none) sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right]))
      (.raised
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode) := by
  have hresult := panValuePcRaisedTwoWordSemanticLift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fieldLeft fieldRight left right
    exception exceptionCode exceptionRel resultExceptionCode compiledLeft
    compiledRight hlookup hcode hbytesInWord hdistinct hrel hsource hcompile
    hcompiledLeft hcompiledRight hexception
  simpa [panValuePcResultRel, panValuePcResultRelWithContextCode,
    panValuePcExceptionResultRelWithContextCode] using
    (show panValueCrepStateRel structs context
        (fun _ => none) sourceGlobals sourceMemory
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) } ∧
      panValuePcExceptionResultRel structs context exceptionRel
        resultExceptionCode (crepPcTwoWordGlobalsLookup bytesInWord)
        sourceGlobals sourceMemory exception
        (.rStruct [.word left, .word right])
        { state with globals :=
            (updateMemory (updateMemory state.globals 0 left)
              (0 + bytesInWord) right) }
        exceptionCode from
      ⟨hresult.2.2.1, hresult.2.2.2.1⟩)

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
    (panValueCrepStateRel structs context (fun _ => none) sourceGlobals
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
          (.rStruct [.word left, .word right])) ≤ 32)) ∧
    lookupInfo exception context.exceptions = some exceptionCode := by
  have hresult := panValuePcRaisedTwoWordResultRel_of_semantic_lift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fieldLeft fieldRight
    left right exception exceptionCode exceptionRel resultExceptionCode
    compiledLeft compiledRight hlookup hcode hbytesInWord hdistinct hrel hsource
    hcompile hcompiledLeft hcompiledRight hexception
  rcases hresult with
    ⟨hpost, spillAddress, code, hresultCode, htargetCode, hcontrol, hpayload⟩
  have hnonempty : 1 ≤ Shape.shapeSize
      (panValueShape structs (.rStruct [.word left, .word right])) := by
    simp [panValueShape, Shape.shapeSize]
  have hshape : Shape.shapeSize
      (panValueShape structs (.rStruct [.word left, .word right])) ≤ 32 := by
    simp [panValueShape, Shape.shapeSize]
  refine ⟨?_, hlookup⟩
  refine ⟨hpost, ?_⟩
  refine ⟨spillAddress, hcontrol, ?_, ?_, ?_⟩
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

theorem panValuePcRaisedHraiseData_of_control_evidence
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hpost : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory targetState)
    (hcontrol : panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException))
    (hcode : exceptionCode sourceException = some targetException)
    (hlookup : 1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException := by
  rcases hcontrol with ⟨spillAddress, hraised⟩
  exact ⟨hpost, spillAddress, hraised, hcode, hlookup, hsize⟩

theorem panValuePcRaisedHraiseData_of_control_evidence_with_context_code
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hpost : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory targetState)
    (hcontrol : panValueCrepControlRel structs context exceptionRel
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException))
    (hcode : exceptionCode sourceException = some targetException)
    (hlookup : 1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
      globalsLookup targetState sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException) :
    panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
  exact ⟨panValuePcRaisedHraiseData_of_control_evidence structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hpost
    hcontrol hcode hlookup hsize, hlookupCode⟩

theorem panValuePcResultRel_of_raised_hraise_data
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hraiseData : panValuePcRaisedHraiseData exceptionCode globalsLookup
      structs context exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) := by
  rcases hraiseData with
    ⟨hpost, spillAddress, hcontrol, hcode, hlookup, hsize⟩
  refine ⟨hpost, ?_⟩
  exact panValuePcExceptionResultRel_of_raised_control structs context
    exceptionRel exceptionCode globalsLookup sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException spillAddress
    hcontrol hcode hlookup hsize

theorem panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hraiseEvidence :
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException := by
  have hresult := panValuePcResultRel_of_raised_hraise_data structs context
      exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException
      hraiseEvidence.1
  exact ⟨hresult.2, hraiseEvidence.2⟩

theorem panValuePcRaisedHraiseData_to_exception_result_rel
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hraiseData : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException) :
    ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
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
  intro sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException hcontrol
  have hresult := panValuePcResultRel_of_raised_hraise_data structs context
    exceptionRel exceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException
    (hraiseData sourceLocals sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException hcontrol)
  simpa [panValuePcResultRel] using hresult

theorem panValuePcRaisedHraiseData_to_exception_result_rel_with_context_code
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hraiseEvidence : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  intro sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException hcontrol
  rcases hraiseEvidence sourceLocals sourceGlobals sourceMemory sourceException
    sourceValue targetState targetException hcontrol with
    ⟨hraiseData, hlookupCode⟩
  have hresult := panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel exceptionCode globalsLookup sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException ⟨hraiseData, hlookupCode⟩
  exact ⟨hraiseData.1, hresult⟩

def crepPcFlatGlobalsLookup [OfNat α 0] [Add α]
    (bytesInWord : α) (state : CrepState α) (value : PanValue α) :
    Option (List α) :=
  readMemoryListAt state.globals 0 bytesInWord
    (panValueFlatWords value).length

theorem crepPcFlatGlobalsLookup_of_stored_flat_words
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (bytesInWord : α) (state : CrepState α) (value : PanValue α)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord
        (panValueFlatWords value).length)) :
    crepPcFlatGlobalsLookup bytesInWord
        { state with globals :=
            (updateMemoryListAt state.globals 0 bytesInWord
              (panValueFlatWords value)) } value =
      some (panValueFlatWords value) := by
  unfold crepPcFlatGlobalsLookup
  exact readMemoryListAt_updateMemoryListAt state.globals 0 bytesInWord
    (panValueFlatWords value) hdistinct

theorem panValuePcRaisedHraiseData_of_flat_spill_state
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (values : List α)
    (state : CrepState α) (bytesInWord targetException : α)
    (sourceValue : PanValue α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hexception : exceptionRel sourceException sourceValue targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
      (fun _ => none) sourceGlobals sourceMemory sourceException sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values }
      targetException := by
  have hpost : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values } := by
    refine ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals, ?_⟩
    exact hrel.2.2
  have hraisedState : panValueCrepRaisedStateRel structs context
      sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values } 0 := by
    exact panValueCrepStateRelExcept_of_state_rel
      structs context (fun _ => none) sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values }
      (fun address => address = 0) hpost
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values }
      targetException 0 := ⟨hraisedState, hexception⟩
  have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord
        (panValueFlatWords sourceValue).length) := by
    simpa [hflat] using hdistinct
  have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
    (α := α) bytesInWord state sourceValue hdistinct'
  refine ⟨hpost, 0, hcontrol, hcode, ?_, hsize⟩
  intro _
  simpa [hflat] using hstored

theorem panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (values : List α)
    (state : CrepState α) (bytesInWord targetException : α)
    (sourceValue : PanValue α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hexception : exceptionRel sourceException sourceValue targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
      sourceLocals sourceGlobals sourceMemory sourceException sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values }
      targetException := by
  let targetState : CrepState α :=
    { state with globals := updateMemoryListAt state.globals 0 bytesInWord values }
  have hpost : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory targetState := by
    refine ⟨hrel.1, hrel.2.1, ?_⟩
    exact hrel.2.2
  have hraisedState : panValueCrepRaisedStateRel structs context
      sourceGlobals sourceMemory targetState 0 := by
    have hpostExcept := panValueCrepStateRelExcept_of_state_rel
      structs context sourceLocals sourceGlobals sourceMemory targetState
      (fun address => address = 0) hpost
    exact ⟨hpost.1, panValueCrepLocalsRel_empty structs context state.locals,
      hpostExcept.2.2⟩
  have hcontrol : panValueCrepRaisedControlRel structs context exceptionRel
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException 0 := ⟨hraisedState, hexception⟩
  have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord
        (panValueFlatWords sourceValue).length) := by
    simpa [hflat] using hdistinct
  have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
    (α := α) bytesInWord state sourceValue hdistinct'
  refine ⟨hpost, 0, hcontrol, hcode, ?_, hsize⟩
  intro _
  simpa [targetState, hflat] using hstored

theorem panValuePcResultRelWithContextCode_of_raised_flat_spill
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (values : List α)
    (state : CrepState α) (bytesInWord targetException : α)
    (sourceValue : PanValue α)
    (hstate : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory state)
    (hexception : exceptionRel sourceException sourceValue targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hlookupCode : lookupInfo sourceException context.exceptions =
      some targetException)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised
        { state with globals :=
            (updateMemoryListAt state.globals 0 bytesInWord values) }
        targetException) := by
  have hraiseData :=
    panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
    structs context exceptionRel exceptionCode sourceLocals sourceGlobals
    sourceMemory sourceException values state bytesInWord targetException sourceValue
    hstate hexception hcode hflat hdistinct hsize
  have hresult := panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel exceptionCode (crepPcFlatGlobalsLookup bytesInWord)
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    { state with globals :=
        (updateMemoryListAt state.globals 0 bytesInWord values) }
    targetException ⟨hraiseData, hlookupCode⟩
  exact ⟨hraiseData.1, hresult⟩

theorem panValuePcRaisedHraiseData_of_flat_spill_state_retarget_globals
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceException : ExceptionId) (values : List α)
    (state : CrepState α) (bytesInWord targetException : α)
    (sourceValue : PanValue α)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hexception : exceptionRel sourceException sourceValue targetException)
    (hcode : exceptionCode sourceException = some targetException)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookup : crepPcFlatGlobalsLookup bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
            updateMemoryListAt state.globals 0 bytesInWord values }
          sourceValue) :
    panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
      sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 bytesInWord values }
      targetException := by
  have hcanonical :=
    panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
    structs context
    exceptionRel exceptionCode sourceLocals sourceGlobals sourceMemory
    sourceException values state bytesInWord targetException sourceValue hrel
    hexception hcode hflat hdistinct hsize
  rcases hcanonical with
    ⟨hpost, spillAddress, hcontrol, hcode, hpayload, hsize⟩
  refine ⟨hpost, spillAddress, hcontrol, hcode, ?_, hsize⟩
  intro hnonempty
  rw [← hlookup]
  exact hpayload hnonempty

/-! Turn the generic structured Raise evaluator theorem into the exact
    raised-result package consumed by `panValuePcCompileCorrect_compact`.
    The evaluator theorem supplies the raised control witness; this adapter
    adds the exception-code and payload-observation obligations at the Pc
    boundary.  The result is intended for the generic `hother` callback, so
    no unsupported payload case is silently discharged. -/
theorem panValuePcRaisedGenericHraise_of_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hlookupPayload :
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
        globalsLookup
            { state with globals :=
                updateMemoryListAt state.globals 0 context.bytesInWord values }
            sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode globalsLookup structs context
      exceptionRel (fun _ => none) sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode ∧ lookupInfo exception context.exceptions = some exceptionCode := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel hlookup hrel
    hsource hvalid hcompile hlength hcompiled hnot hfresh hexception
  rcases hgeneric with ⟨_, _, hcontrol⟩
  have hpost : panValueCrepStateRel structs context
      (fun _ => none) sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values } := by
    have hraisedState := hcontrol.1
    refine ⟨hrel.1, hraisedState.2.1, ?_⟩
    exact hrel.2.2
  exact ⟨⟨hpost, 0, hcontrol, hcode, hlookupPayload, hsize⟩, hlookup⟩

theorem panValuePcRaisedGenericHraise_of_evidence_with_source_locals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hlookupPayload :
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
        globalsLookup
            { state with globals :=
                updateMemoryListAt state.globals 0 context.bytesInWord values }
            sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode ∧ lookupInfo exception context.exceptions = some exceptionCode := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel hlookup hrel
    hsource hvalid hcompile hlength hcompiled hnot hfresh hexception
  rcases hgeneric with ⟨_, _, hcontrol⟩
  have hpost : panValueCrepStateRel structs context sourceLocals
      sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values } := by
    refine ⟨hrel.1, hrel.2.1, ?_⟩
    exact hrel.2.2
  exact ⟨⟨hpost, 0, hcontrol, hcode, hlookupPayload, hsize⟩, hlookup⟩

theorem panValuePcResultRel_of_raised_generic_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hlookupPayload :
      1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
        globalsLookup
            { state with globals :=
                updateMemoryListAt state.globals 0 context.bytesInWord values }
            sourceValue = some (panValueFlatWords sourceValue))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      globalsLookup
      (.raised (fun _ => none) sourceGlobals sourceMemory exception sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  apply panValuePcResultRel_of_raised_hraise_data
  exact (panValuePcRaisedGenericHraise_of_evidence context structs
    sourceFunctions functions sourceLocals sourceGlobals sourceMemory state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel exception exceptionCode expression sourceValue
    compiled shape values exceptionRel resultExceptionCode globalsLookup hlookup
    hrel hsource hvalid hcompile hlength hcompiled hnot hfresh hexception hcode
    hlookupPayload hsize).1

theorem panValuePcRaisedGenericHraise_of_flat_globals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hvalues : values = panValueFlatWords sourceValue)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord
        (panValueFlatWords sourceValue).length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord) structs context
      exceptionRel (fun _ => none) sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          (updateMemoryListAt state.globals 0 context.bytesInWord values) }
      exceptionCode := by
  exact (panValuePcRaisedGenericHraise_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    (crepPcFlatGlobalsLookup context.bytesInWord) hlookup hrel hsource hvalid
    hcompile hlength hcompiled hnot hfresh hexception hcode (by
      intro _
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        context.bytesInWord state sourceValue hdistinct
      simpa [hvalues] using hstored) hsize).1

theorem panValuePcRaisedHraiseData_retarget_globals_lookup
    [OfNat α 0] [Add α]
    (bytesInWord : α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hlookup : crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
      globalsLookup targetState sourceValue)
    (hraiseData : panValuePcRaisedHraiseData exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
      sourceLocals sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException) :
    panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException := by
  rcases hraiseData with
    ⟨hpost, spillAddress, hcontrol, hcode, hpayload, hsize⟩
  refine ⟨hpost, spillAddress, hcontrol, hcode, ?_, hsize⟩
  intro hnonempty
  rw [← hlookup]
  exact hpayload hnonempty

/-! Lift an entire canonical raised-data callback through an extensionally
    equal HOL global lookup.  This is the callback-level adapter needed by
    the compact `pc_compile_correct` boundary; it preserves every other
    raised-state, exception-code, and payload obligation unchanged. -/
theorem panValuePcRaisedHraiseData_retarget_globals_callback
    [OfNat α 0] [Add α]
    (bytesInWord : α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
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
  exact panValuePcRaisedHraiseData_retarget_globals_lookup
    bytesInWord exceptionCode globalsLookup structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException (hlookup targetState sourceValue)
    (hraiseData context structs exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException hcontrol)

theorem panValuePcRaisedHraiseData_retarget_globals_callback_with_context_code
    [OfNat α 0] [Add α]
    (bytesInWord : α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  have hcanonical := hraiseEvidence context structs exceptionRel sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState targetException
    hcontrol
  exact ⟨panValuePcRaisedHraiseData_retarget_globals_lookup bytesInWord
    exceptionCode globalsLookup structs context exceptionRel sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException (hlookup targetState sourceValue) hcanonical.1, hcanonical.2⟩

theorem panValuePcResultRel_of_raised_generic_flat_evidence_retarget_globals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hvalues : values = panValueFlatWords sourceValue)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord
        (panValueFlatWords sourceValue).length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hcanonical := panValuePcRaisedGenericHraise_of_evidence_with_source_locals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    globalsLookup hlookup hrel hsource hvalid hcompile hlength hcompiled hnot hfresh
    hexception hcode (by
      intro _
      have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord
            (panValueFlatWords sourceValue).length) := by
        simpa [hvalues] using hdistinct
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := α) context.bytesInWord state sourceValue hdistinct'
      rw [← hlookupGlobals]
      simpa [hvalues] using hstored) hsize
  exact panValuePcResultRel_of_raised_hraise_data structs context exceptionRel
    resultExceptionCode globalsLookup sourceLocals sourceGlobals
    sourceMemory exception sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode hcanonical.1

theorem panValuePcResultRel_of_raised_hraise_data_retarget_globals_lookup
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) (bytesInWord : α)
    (hlookup : crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
      globalsLookup targetState sourceValue)
    (hraiseData : panValuePcRaisedHraiseData exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
      sourceLocals sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException) :
    panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) := by
  exact panValuePcResultRel_of_raised_hraise_data structs context exceptionRel
    exceptionCode globalsLookup sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException
    (panValuePcRaisedHraiseData_retarget_globals_lookup bytesInWord
      exceptionCode globalsLookup structs context exceptionRel sourceLocals
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException hlookup hraiseData)

theorem panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data_retarget_globals_lookup
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) (bytesInWord : α)
    (hlookup : crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
      globalsLookup targetState sourceValue)
    (hraiseEvidence :
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
      sourceValue targetState targetException := by
  have hretarget := panValuePcRaisedHraiseData_retarget_globals_lookup
    bytesInWord exceptionCode globalsLookup structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException hlookup hraiseEvidence.1
  exact panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel exceptionCode globalsLookup sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException ⟨hretarget, hraiseEvidence.2⟩

theorem panValuePcResultRelWithContextCode_of_raised_hraise_data_retarget_globals_lookup
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α) (bytesInWord : α)
    (hlookup : crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
      globalsLookup targetState sourceValue)
    (hraiseEvidence :
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) := by
  refine ⟨hraiseEvidence.1.1, ?_⟩
  exact panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data_retarget_globals_lookup
    structs context exceptionRel exceptionCode globalsLookup sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException bytesInWord hlookup hraiseEvidence

theorem panValuePcRaisedThreeWordHraise_of_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode first second third : α)
    (expression : Exp α)
    (compiledFirst compiledSecond compiledThird : CrepExp α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct [.word first, .word second, .word third]))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct [.word first, .word second, .word third]) = true)
    (hcompile : compileExp context expression =
      ([compiledFirst, compiledSecond, compiledThird],
        .comb [.one, .one, .one]))
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress
      [compiledFirst, compiledSecond, compiledThird] =
      some [first, second, third])
    (hnot : ∀ name ∈ freshNames context
      [compiledFirst, compiledSecond, compiledThird].length 1,
      ∀ value ∈ [compiledFirst, compiledSecond, compiledThird],
        name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context
      [compiledFirst, compiledSecond, compiledThird].length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct [.word first, .word second, .word third]) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct01 : (0 : α) ≠ 0 + context.bytesInWord)
    (hdistinct02 : (0 : α) ≠
      (0 + context.bytesInWord) + context.bytesInWord)
    (hdistinct12 : (0 : α) + context.bytesInWord ≠
      (0 + context.bytesInWord) + context.bytesInWord) :
    (panValuePcRaisedHraiseData resultExceptionCode
        (crepPcThreeWordGlobalsLookup context.bytesInWord) structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory exception
        (.rStruct [.word first, .word second, .word third])
        { state with globals :=
            (updateMemoryListAt state.globals 0 context.bytesInWord
              [first, second, third]) }
        exceptionCode) ∧
      lookupInfo exception context.exceptions = some exceptionCode := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression (.rStruct [.word first, .word second, .word third])
    [compiledFirst, compiledSecond, compiledThird]
    (.comb [.one, .one, .one]) [first, second, third] exceptionRel hlookup hrel
    hsource hvalid hcompile (by simp [Shape.shapeSize]) hcompiled hnot hfresh hexception
  rcases hgeneric with ⟨_, _, hcontrol⟩
  have hpost : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory
      { state with globals :=
          (updateMemoryListAt state.globals 0 context.bytesInWord
            [first, second, third]) } := by
    refine ⟨hrel.1, hrel.2.1, ?_⟩
    exact hrel.2.2
  have hlookupPayload :
      1 ≤ Shape.shapeSize (panValueShape structs
        (.rStruct [.word first, .word second, .word third])) →
      crepPcThreeWordGlobalsLookup context.bytesInWord
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                [first, second, third]) }
          (.rStruct [.word first, .word second, .word third]) =
        some (panValueFlatWords
          (.rStruct [.word first, .word second, .word third])) := by
    intro _
    simp [crepPcThreeWordGlobalsLookup, panValueFlatWords,
      panValueFlatWordsFuel, panValueFlatValueFuel,
      panValueFlatWordsFuel.panValueFlatWordsListFuel,
      panValueFlatValueFuel.panValueFlatValueListFuel,
      updateMemoryListAt, updateMemory, hdistinct01, hdistinct02,
      hdistinct12]
  have hsize : Shape.shapeSize (panValueShape structs
      (.rStruct [.word first, .word second, .word third])) ≤ 32 := by
    simp [panValueShape, Shape.shapeSize]
  refine ⟨?_, hlookup⟩
  exact ⟨hpost, 0, hcontrol, hcode, hlookupPayload, hsize⟩

theorem panValuePcRaisedThreeWordSemanticLift
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode first second third : α)
    (expression : Exp α)
    (compiledFirst compiledSecond compiledThird : CrepExp α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct [.word first, .word second, .word third]))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct [.word first, .word second, .word third]) = true)
    (hcompile : compileExp context expression =
      ([compiledFirst, compiledSecond, compiledThird],
        .comb [.one, .one, .one]))
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress
      [compiledFirst, compiledSecond, compiledThird] =
      some [first, second, third])
    (hnot : ∀ name ∈ freshNames context
      [compiledFirst, compiledSecond, compiledThird].length 1,
      ∀ value ∈ [compiledFirst, compiledSecond, compiledThird],
        name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context
      [compiledFirst, compiledSecond, compiledThird].length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct [.word first, .word second, .word third]) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct01 : (0 : α) ≠ 0 + context.bytesInWord)
    (hdistinct02 : (0 : α) ≠
      (0 + context.bytesInWord) + context.bytesInWord)
    (hdistinct12 : (0 : α) + context.bytesInWord ≠
      (0 + context.bytesInWord) + context.bytesInWord) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct [.word first, .word second, .word third])) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      ([compiledFirst, compiledSecond, compiledThird].length +
        (freshNames context [compiledFirst, compiledSecond, compiledThird].length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            (updateMemoryListAt state.globals 0 context.bytesInWord
              [first, second, third]) }
        exceptionCode) ∧
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
      (crepPcThreeWordGlobalsLookup context.bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory exception
      (.rStruct [.word first, .word second, .word third]))
      (.raised
        { state with globals :=
            (updateMemoryListAt state.globals 0 context.bytesInWord
              [first, second, third]) }
        exceptionCode) := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression (.rStruct [.word first, .word second, .word third])
    [compiledFirst, compiledSecond, compiledThird]
    (.comb [.one, .one, .one]) [first, second, third] exceptionRel hlookup hrel
    hsource hvalid hcompile (by simp [Shape.shapeSize]) hcompiled hnot hfresh
    hexception
  have hraiseData := panValuePcRaisedThreeWordHraise_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode first
    second third expression compiledFirst compiledSecond compiledThird exceptionRel
    resultExceptionCode hlookup hrel hsource hvalid hcompile hcompiled hnot hfresh
    hexception hcode hdistinct01 hdistinct02 hdistinct12
  rcases hgeneric with ⟨hsourceEval, htargetEval, _hcontrol⟩
  have hresult := panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel resultExceptionCode
    (crepPcThreeWordGlobalsLookup context.bytesInWord) sourceLocals
    sourceGlobals sourceMemory exception
    (.rStruct [.word first, .word second, .word third])
    { state with globals :=
        (updateMemoryListAt state.globals 0 context.bytesInWord
          [first, second, third]) }
    exceptionCode hraiseData
  have hcontext : panValuePcResultRelWithContextCode structs context
      exceptionRel resultExceptionCode
      (crepPcThreeWordGlobalsLookup context.bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct [.word first, .word second, .word third]))
      (.raised
        { state with globals :=
            (updateMemoryListAt state.globals 0 context.bytesInWord
              [first, second, third]) }
        exceptionCode) := by
    simpa [panValuePcResultRelWithContextCode] using
      (show panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                [first, second, third]) } ∧
        panValuePcExceptionResultRelWithContextCode structs context exceptionRel
          resultExceptionCode (crepPcThreeWordGlobalsLookup context.bytesInWord)
          sourceGlobals sourceMemory exception
          (.rStruct [.word first, .word second, .word third])
          { state with globals :=
              (updateMemoryListAt state.globals 0 context.bytesInWord
                [first, second, third]) }
          exceptionCode from
        ⟨hraiseData.1.1, hresult⟩)
  exact ⟨hsourceEval, htargetEval, hcontext⟩

/-! The same canonical spill adapter for a raw record of any number of word
    fields.  This is the generic structured payload route used by the
    unsupported branch of the compact dispatcher once evaluator evidence is
    available; the specialized one-, two-, and three-word adapters above keep
    their smaller obligations. -/
theorem panValuePcRaisedRawWordListHraise_of_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (values : List α) (expression : Exp α)
    (compiled : List (CrepExp α)) (shape : Shape)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct (values.map (fun value => .word value))) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize
      (panValueShape structs (.rStruct (values.map (fun value => .word value)))) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord) structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory exception
      (.rStruct (values.map (fun value => .word value)))
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode ∧ lookupInfo exception context.exceptions = some exceptionCode := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression (.rStruct (values.map (fun value => .word value)))
    compiled shape values exceptionRel hlookup hrel hsource hvalid hcompile hlength
    hcompiled hnot hfresh hexception
  rcases hgeneric with ⟨_, _, hcontrol⟩
  have hpost : panValueCrepStateRel structs context
      sourceLocals sourceGlobals sourceMemory
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values } := by
    refine ⟨hrel.1, hrel.2.1, ?_⟩
    exact hrel.2.2
  have hlookupPayload :
      1 ≤ Shape.shapeSize (panValueShape structs
        (.rStruct (values.map (fun value => .word value)))) →
      crepPcFlatGlobalsLookup context.bytesInWord
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values }
          (.rStruct (values.map (fun value => .word value))) =
        some (panValueFlatWords
          (.rStruct (values.map (fun value => .word value)))) := by
    intro _
    have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
        (storeAddresses (0 : α) context.bytesInWord
          (panValueFlatWords
            (.rStruct (values.map (fun value => .word value)))).length) := by
      simpa [panValueFlatWords_rStruct_word_list] using hdistinct
    simpa [panValueFlatWords_rStruct_word_list] using
      (crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := α) context.bytesInWord state
        (.rStruct (values.map (fun value => .word value))) hdistinct')
  exact ⟨⟨hpost, 0, hcontrol, hcode, hlookupPayload, hsize⟩, hlookup⟩

theorem panValuePcRaisedRawWordListSemanticLift
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (values : List α) (expression : Exp α)
    (compiled : List (CrepExp α)) (shape : Shape)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct (values.map (fun value => .word value))) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize
      (panValueShape structs (.rStruct (values.map (fun value => .word value)))) ≤ 32) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct (values.map (fun value => .word value)))) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValuePcResultRelWithContextCode structs context exceptionRel resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct (values.map (fun value => .word value))))
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression (.rStruct (values.map (fun value => .word value))) compiled shape
    values exceptionRel hlookup hrel hsource hvalid hcompile hlength hcompiled
    hnot hfresh hexception
  have hraiseData := panValuePcRaisedRawWordListHraise_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode values
    expression compiled shape exceptionRel resultExceptionCode hlookup hrel hsource
    hvalid hcompile hlength hcompiled hnot hfresh hexception hcode hdistinct hsize
  rcases hgeneric with ⟨hsourceEval, htargetEval, _hcontrol⟩
  have hresult := panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel resultExceptionCode
    (crepPcFlatGlobalsLookup context.bytesInWord) sourceLocals sourceGlobals
    sourceMemory exception (.rStruct (values.map (fun value => .word value)))
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode hraiseData
  have hcontext : panValuePcResultRelWithContextCode structs context
      exceptionRel resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct (values.map (fun value => .word value))))
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
    simpa [panValuePcResultRelWithContextCode] using
      (show panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        panValuePcExceptionResultRelWithContextCode structs context exceptionRel
          resultExceptionCode (crepPcFlatGlobalsLookup context.bytesInWord)
          sourceGlobals sourceMemory exception
          (.rStruct (values.map (fun value => .word value)))
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values }
          exceptionCode from
        ⟨hraiseData.1.1, hresult⟩)
  exact ⟨hsourceEval, htargetEval, hcontext⟩

theorem panValuePcRaisedRawWordListSemanticLift_retarget_globals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (values : List α) (expression : Exp α)
    (compiled : List (CrepExp α)) (shape : Shape)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct (values.map (fun value => .word value))) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize
      (panValueShape structs (.rStruct (values.map (fun value => .word value)))) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value))) =
      globalsLookup
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value)))) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct (values.map (fun value => .word value)))) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValuePcResultRel structs context exceptionRel resultExceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct (values.map (fun value => .word value))))
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hsemantic := panValuePcRaisedRawWordListSemanticLift
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode values
    expression compiled shape exceptionRel resultExceptionCode hlookup hrel hsource
    hvalid hcompile hlength hcompiled hnot hfresh hexception hcode hdistinct hsize
  have hraiseData := panValuePcRaisedRawWordListHraise_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode values
    expression compiled shape exceptionRel resultExceptionCode hlookup hrel hsource
    hvalid hcompile hlength hcompiled hnot hfresh hexception hcode hdistinct hsize
  have hresult := panValuePcResultRel_of_raised_hraise_data_retarget_globals_lookup
    structs context exceptionRel resultExceptionCode globalsLookup
    sourceLocals sourceGlobals sourceMemory exception
    (.rStruct (values.map (fun value => .word value)))
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode context.bytesInWord hlookupGlobals hraiseData.1
  exact ⟨hsemantic.1, hsemantic.2.1, hresult⟩

/-! Preserve the exact Cake exception-code lookup alongside the evaluator-backed
    raw-word semantic lift.  This is the direct semantic adapter consumed by
    the context-code form of the compact `pc_compile_correct` boundary. -/
theorem panValuePcRaisedRawWordListSemanticLift_retarget_globals_with_context_code
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (values : List α) (expression : Exp α)
    (compiled : List (CrepExp α)) (shape : Shape)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct (values.map (fun value => .word value))) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize
      (panValueShape structs (.rStruct (values.map (fun value => .word value)))) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value))) =
      globalsLookup
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value)))) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception (.rStruct (values.map (fun value => .word value)))) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValuePcResultRelWithContextCode structs context exceptionRel
      resultExceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct (values.map (fun value => .word value))))
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hsemantic := panValuePcRaisedRawWordListSemanticLift_retarget_globals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode values
    expression compiled shape exceptionRel resultExceptionCode globalsLookup hlookup
    hrel hsource hvalid hcompile hlength hcompiled hnot hfresh hexception hcode
    hdistinct hsize hlookupGlobals
  have hresult : panValuePcResultRelWithContextCode structs context
      exceptionRel resultExceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception
        (.rStruct (values.map (fun value => .word value))))
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
    simpa [panValuePcResultRelWithContextCode] using
      (show panValueCrepStateRel structs context sourceLocals
          sourceGlobals sourceMemory
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        panValuePcExceptionResultRelWithContextCode structs context exceptionRel
          resultExceptionCode globalsLookup sourceGlobals
          sourceMemory exception (.rStruct (values.map (fun value => .word value)))
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values }
          exceptionCode from
        ⟨hsemantic.2.2.1, hsemantic.2.2.2, hlookup⟩)
  exact ⟨hsemantic.1, hsemantic.2.1, hresult⟩

theorem panValuePcResultRelWithContextCode_of_raised_result_rel
    [BEq α] [LawfulBEq α]
    (structs : StructContext) (context : CompileContext α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
    (sourceValue : PanValue α) (targetState : CrepState α)
    (targetException : α)
    (hresultEvidence :
      panValuePcResultRel structs context exceptionRel exceptionCode globalsLookup
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    panValuePcResultRelWithContextCode structs context exceptionRel exceptionCode
      globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
      (.raised targetState targetException) := by
  simpa [panValuePcResultRelWithContextCode] using
    (show panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException from
      ⟨hresultEvidence.1.1, hresultEvidence.1.2, hresultEvidence.2⟩)

/-! Direct result-boundary form of the raw word-list evidence.  This is the
    evaluator-backed lift used by compact `pc_compile_correct` callers that
    need both the flattened global observation and Cake's exception lookup. -/
theorem panValuePcExceptionResultRelWithContextCode_of_raised_raw_word_list_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (values : List α) (expression : Exp α)
    (compiled : List (CrepExp α)) (shape : Shape)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression =
      some (.rStruct (values.map (fun value => .word value))))
    (hvalid : panValuePayloadWithinLimit structs
      (.rStruct (values.map (fun value => .word value))) = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception
      (.rStruct (values.map (fun value => .word value))) exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize
      (panValueShape structs (.rStruct (values.map (fun value => .word value)))) ≤ 32) :
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value))) =
      globalsLookup
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        (.rStruct (values.map (fun value => .word value)))) →
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      resultExceptionCode globalsLookup
      sourceGlobals sourceMemory exception
      (.rStruct (values.map (fun value => .word value)))
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode := by
  intro hlookupGlobals
  have hcanonical := panValuePcRaisedRawWordListHraise_of_evidence
      context structs sourceFunctions functions sourceLocals sourceGlobals
      sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
      baseAddress topAddress bytesInWord sourceFuel exception exceptionCode values
      expression compiled shape exceptionRel resultExceptionCode hlookup hrel
      hsource hvalid hcompile hlength hcompiled hnot hfresh hexception hcode
      hdistinct hsize
  have hretarget := panValuePcRaisedHraiseData_retarget_globals_lookup
    context.bytesInWord resultExceptionCode globalsLookup structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory exception
    (.rStruct (values.map (fun value => .word value)))
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode hlookupGlobals hcanonical.1
  exact panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel resultExceptionCode globalsLookup
    sourceLocals sourceGlobals sourceMemory exception
    (.rStruct (values.map (fun value => .word value)))
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode ⟨hretarget, hcanonical.2⟩

/-! General evaluator-backed raised data with the canonical flattened global
    lookup.  The raw-word-list theorem above is the common flat specialization;
    this version keeps nested or otherwise non-flat source payloads available
    when their evaluator and flattening evidence is explicit. -/
theorem panValuePcRaisedGenericHraise_of_evidence_flat_globals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord) structs context
      exceptionRel (fun _ => none) sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode := by
  have hpaired := panValuePcRaisedGenericHraise_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel
    resultExceptionCode (crepPcFlatGlobalsLookup context.bytesInWord)
    hlookup hrel hsource hvalid hcompile hlength hcompiled
    hnot hfresh hexception hcode (by
      intro _
      have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord
            (panValueFlatWords sourceValue).length) := by
        simpa [hflat] using hdistinct
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := α) context.bytesInWord state sourceValue hdistinct'
      simpa [hflat] using hstored) hsize
  exact hpaired.1

theorem panValuePcRaisedGenericHraise_of_evidence_flat_globals_with_source_locals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    panValuePcRaisedHraiseData resultExceptionCode
      (crepPcFlatGlobalsLookup context.bytesInWord) structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode := by
  have hpaired := panValuePcRaisedGenericHraise_of_evidence_with_source_locals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    (crepPcFlatGlobalsLookup context.bytesInWord)
    hlookup hrel hsource hvalid hcompile hlength hcompiled hnot hfresh hexception
    hcode (by
      intro _
      have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord
            (panValueFlatWords sourceValue).length) := by
        simpa [hflat] using hdistinct
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := α) context.bytesInWord state sourceValue hdistinct'
      simpa [hflat] using hstored) hsize
  exact hpaired.1

/-! Lift generic evaluator-backed raised evidence through the caller's HOL
    global lookup.  The canonical compiler lookup remains the source of the
    payload proof; only the extensional lookup equation is used at this
    boundary. -/
theorem panValuePcRaisedGenericHraise_of_evidence_retarget_globals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    panValuePcRaisedHraiseData resultExceptionCode globalsLookup structs context
      exceptionRel (fun _ => none) sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode := by
  have hcanonical := panValuePcRaisedGenericHraise_of_evidence_flat_globals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    hlookup hrel hsource hvalid hcompile hlength hcompiled hnot hfresh hexception
    hcode hflat hdistinct hsize
  exact panValuePcRaisedHraiseData_retarget_globals_lookup
    context.bytesInWord resultExceptionCode globalsLookup structs context
    exceptionRel (fun _ => none) sourceGlobals sourceMemory exception sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode hlookupGlobals hcanonical

theorem panValuePcRaisedGenericHraise_of_evidence_retarget_globals_with_source_locals
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    panValuePcRaisedHraiseData resultExceptionCode globalsLookup structs context
      exceptionRel sourceLocals sourceGlobals sourceMemory exception sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode ∧ lookupInfo exception context.exceptions = some exceptionCode := by
  have hcanonical := panValuePcRaisedGenericHraise_of_evidence_with_source_locals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    globalsLookup hlookup hrel hsource hvalid hcompile hlength hcompiled hnot
    hfresh hexception hcode (by
      intro _
      have hdistinct' : List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord
            (panValueFlatWords sourceValue).length) := by
        simpa [hflat] using hdistinct
      have hstored := crepPcFlatGlobalsLookup_of_stored_flat_words
        (α := α) context.bytesInWord state sourceValue hdistinct'
      rw [← hlookupGlobals]
      simpa [hflat] using hstored) hsize
  exact hcanonical

theorem panValuePcExceptionResultRelWithContextCode_of_raised_generic_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    panValuePcExceptionResultRelWithContextCode structs context exceptionRel
      resultExceptionCode globalsLookup sourceGlobals sourceMemory exception
      sourceValue
      { state with globals :=
          updateMemoryListAt state.globals 0 context.bytesInWord values }
      exceptionCode := by
  have hraiseData := panValuePcRaisedGenericHraise_of_evidence_retarget_globals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    globalsLookup hlookup hrel hsource hvalid hcompile hlength hcompiled hnot
    hfresh hexception hcode hflat hdistinct hsize hlookupGlobals
  exact panValuePcExceptionResultRelWithContextCode_of_raised_hraise_data
    structs context exceptionRel resultExceptionCode globalsLookup (fun _ => none)
    sourceGlobals sourceMemory exception sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode ⟨hraiseData, hlookup⟩

theorem panValuePcResultRelWithContextCode_of_raised_generic_evidence
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    panValuePcResultRelWithContextCode structs context exceptionRel
      resultExceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hraiseData :=
    panValuePcRaisedGenericHraise_of_evidence_retarget_globals_with_source_locals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    globalsLookup hlookup hrel hsource hvalid hcompile hlength hcompiled hnot hfresh
    hexception hcode hflat hdistinct hsize hlookupGlobals
  have hresult := panValuePcResultRel_of_raised_hraise_data
    structs context exceptionRel resultExceptionCode globalsLookup sourceLocals
    sourceGlobals sourceMemory exception sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode hraiseData.1
  exact panValuePcResultRelWithContextCode_of_raised_result_rel
    structs context exceptionRel resultExceptionCode globalsLookup sourceLocals
    sourceGlobals sourceMemory exception sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    exceptionCode ⟨hresult, hlookup⟩

/-! Combine the generic Raise evaluator equations with the exact Pc raised
    result relation.  Unlike the flat-list specialization, this preserves the
    arbitrary structured payload supplied by the evaluator while still
    carrying Cake's `lookupInfo` exception-code provenance. -/
theorem panValuePcRaisedGenericSemanticLift_retarget_globals_with_context_code
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)
    (hlookupGlobals : crepPcFlatGlobalsLookup context.bytesInWord
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        sourceValue = globalsLookup
          { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
          sourceValue) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception sourceValue) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValuePcResultRelWithContextCode structs context exceptionRel
      resultExceptionCode globalsLookup
      (.raised sourceLocals sourceGlobals sourceMemory exception sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have hgeneric := compile_full_pan_value_raise_state_relation_of_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel hlookup hrel hsource
    hvalid hcompile hlength hcompiled hnot hfresh hexception
  have hcontext := panValuePcResultRelWithContextCode_of_raised_generic_evidence
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    globalsLookup hlookup hrel hsource hvalid hcompile hlength hcompiled hnot hfresh
    hexception hcode hflat hdistinct hsize hlookupGlobals
  rcases hgeneric with ⟨hsourceEval, htargetEval, _hcontrol⟩
  exact ⟨hsourceEval, htargetEval, hcontext⟩

/-! Canonical specialization of the generic semantic lift.  The compiler's
    flattened global lookup is discharged from the stored payload and its
    non-aliasing addresses, leaving callers no separate lookup obligation. -/
theorem panValuePcRaisedGenericSemanticLift_flat_globals_with_context_code
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
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (exception : ExceptionId) (exceptionCode : α)
    (expression : Exp α) (sourceValue : PanValue α)
    (compiled : List (CrepExp α)) (shape : Shape) (values : List α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (resultExceptionCode : ExceptionId → Option α)
    (hlookup : lookupInfo exception context.exceptions = some exceptionCode)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some sourceValue)
    (hvalid : panValuePayloadWithinLimit structs sourceValue = true)
    (hcompile : compileExp context expression = (compiled, shape))
    (hlength : compiled.length = Shape.shapeSize shape)
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some values)
    (hnot : ∀ name ∈ freshNames context compiled.length 1,
      ∀ value ∈ compiled, name ∉ crepExpVars value)
    (hfresh : ∀ name ∈ freshNames context compiled.length 1,
      state.locals name = none)
    (hexception : exceptionRel exception sourceValue exceptionCode)
    (hcode : resultExceptionCode exception = some exceptionCode)
    (hflat : panValueFlatWords sourceValue = values)
    (hdistinct : List.Pairwise (fun left right : α => left ≠ right)
      (storeAddresses (0 : α) context.bytesInWord values.length))
    (hsize : Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.raise exception expression) =
      some (.raised (fun _ => none) sourceGlobals sourceMemory
        exception sourceValue) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress
      (values.length + (freshNames context compiled.length 1).length + 2)
      state (compileProg context (.raise exception expression)) =
      some (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) ∧
    panValuePcResultRelWithContextCode structs context exceptionRel
      resultExceptionCode (crepPcFlatGlobalsLookup context.bytesInWord)
      (.raised sourceLocals sourceGlobals sourceMemory exception sourceValue)
      (.raised
        { state with globals :=
            updateMemoryListAt state.globals 0 context.bytesInWord values }
        exceptionCode) := by
  have h := panValuePcRaisedGenericSemanticLift_retarget_globals_with_context_code
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel exception exceptionCode
    expression sourceValue compiled shape values exceptionRel resultExceptionCode
    (crepPcFlatGlobalsLookup context.bytesInWord) hlookup hrel hsource hvalid
    hcompile hlength hcompiled hnot hfresh hexception hcode hflat hdistinct hsize
    (by rfl)
  exact h

/-! A boundary dispatcher that exposes evaluator-backed raw records directly.
    Unlike the legacy dispatcher, its fallback cannot be reached for any
    record whose fields are all words; those records use the canonical
    flattened global-spill theorem above. -/
theorem panValuePcRaisedHraiseCases_with_raw_word_lists
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
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
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
  classical
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  cases sourceValue with
  | word value =>
      exact hword context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException value targetState targetException hcontrol
  | rStruct fields =>
      by_cases hflat : ∃ values : List α,
          fields = values.map (fun value => .word value)
      · rcases hflat with ⟨values, hfields⟩
        subst fields
        exact hraw context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException values targetState targetException hcontrol
      · apply hother context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException (.rStruct fields) targetState targetException
        · intro value hvalue
          simp at hvalue
        · intro values hvalue
          apply hflat
          injection hvalue with hfields
          exact ⟨values, hfields⟩
        · exact hcontrol
  | nStruct name fields =>
      exact hother context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException (.nStruct name fields) targetState targetException
        (by simp)
        (by
          intro values hvalue
          cases hvalue)
        hcontrol

/-! Retarget the raw-word dispatcher from the compiler's canonical flattened
    global lookup to an extensionally equal HOL lookup. -/
theorem panValuePcRaisedHraiseCases_with_raw_word_lists_retarget_globals
    [OfNat α 0] [Add α]
    (bytesInWord : α)
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hword : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (value : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException
        (.word value) targetState targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
    ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  apply panValuePcRaisedHraiseData_retarget_globals_lookup bytesInWord
    exceptionCode globalsLookup structs context exceptionRel sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException (hlookup targetState sourceValue)
  exact panValuePcRaisedHraiseCases_with_raw_word_lists
    exceptionCode (crepPcFlatGlobalsLookup bytesInWord) hword hraw hother
    context structs
    exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
    sourceValue targetState targetException hcontrol

/-! The raw-word dispatcher also preserves the state relation and exact
    exception-code provenance required by the Pc result boundary.  This keeps
    arbitrary-length flat records on the same path as the specialized word,
    two-word, and three-word adapters. -/
theorem panValuePcRaisedHraiseCases_with_raw_word_lists_to_exception_result_rel_with_context_code
    [BEq α] [LawfulBEq α]
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    ∀ (context : CompileContext α) (structs : StructContext)
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
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  have hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
    intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException hcontrol
    cases sourceValue with
    | word value =>
        exact hword context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException value targetState targetException hcontrol
    | rStruct fields =>
        by_cases hflat : ∃ values : List α,
            fields = values.map (fun value => .word value)
        · rcases hflat with ⟨values, hfields⟩
          subst fields
          exact hraw context structs exceptionRel sourceLocals sourceGlobals
            sourceMemory sourceException values targetState targetException hcontrol
        · apply hother context structs exceptionRel sourceLocals sourceGlobals
            sourceMemory sourceException (.rStruct fields) targetState targetException
          · intro value hvalue
            simp at hvalue
          · intro values hvalue
            apply hflat
            injection hvalue with hfields
            exact ⟨values, hfields⟩
          · exact hcontrol
    | nStruct name fields =>
        exact hother context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException (.nStruct name fields) targetState targetException
          (by simp)
          (by
            intro values hvalue
            cases hvalue)
          hcontrol
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  exact panValuePcRaisedHraiseData_to_exception_result_rel_with_context_code
    structs context exceptionRel exceptionCode globalsLookup
    (fun sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException hcontrol =>
      hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException hcontrol

theorem panValuePcRaisedHraiseCases_with_raw_word_lists_paired
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
  classical
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  cases sourceValue with
  | word value =>
      exact hword context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException value targetState targetException hcontrol
  | rStruct fields =>
      by_cases hflat : ∃ values : List α,
          fields = values.map (fun value => .word value)
      · rcases hflat with ⟨values, hfields⟩
        subst fields
        exact hraw context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException values targetState targetException hcontrol
      · apply hother context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException (.rStruct fields) targetState targetException
        · intro value hvalue
          simp at hvalue
        · intro values hvalue
          apply hflat
          injection hvalue with hfields
          exact ⟨values, hfields⟩
        · exact hcontrol
  | nStruct name fields =>
      exact hother context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException (.nStruct name fields) targetState targetException
        (by simp)
        (by
          intro values hvalue
          cases hvalue)
        hcontrol

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
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException)
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
                          cases tail' with
                          | nil =>
                              cases third with
                              | word thirdValue =>
                                  exact hthree context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException left right thirdValue
                                    targetState targetException hcontrol
                              | rStruct fields =>
                                  exact hother context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException
                                    (.rStruct
                                      [.word left, .word right,
                                        .rStruct fields]) targetState targetException
                                    (by
                                      intro value h
                                      nomatch h)
                                    (by
                                      intro left' right' h
                                      have hlen := congrArg
                                        (fun value : PanValue α =>
                                          match value with
                                          | .word _ => 0
                                          | .rStruct values => values.length
                                          | .nStruct _ values => values.length) h
                                      simp at hlen) hcontrol
                              | nStruct name fields =>
                                  exact hother context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException
                                    (.rStruct
                                      [.word left, .word right,
                                        .nStruct name fields]) targetState targetException
                                    (by
                                      intro value h
                                      nomatch h)
                                    (by
                                      intro left' right' h
                                      have hlen := congrArg
                                        (fun value : PanValue α =>
                                          match value with
                                          | .word _ => 0
                                          | .rStruct values => values.length
                                          | .nStruct _ values => values.length) h
                                      simp at hlen) hcontrol
                          | cons fourth tail'' =>
                              exact hother context structs exceptionRel
                                sourceLocals sourceGlobals sourceMemory
                                sourceException
                                  (.rStruct
                                  (.word left :: .word right :: third ::
                                    fourth :: tail'')) targetState targetException
                                (by
                                  intro value h
                                  nomatch h)
                                (by
                                  intro left' right' h
                                  have hlen := congrArg
                                    (fun value : PanValue α =>
                                      match value with
                                      | .word _ => 0
                                      | .rStruct values => values.length
                                      | .nStruct _ values => values.length) h
                                  simp at hlen) hcontrol
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

theorem panValuePcRaisedHraiseCases_paired
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        (.rStruct [.word left, .word right]) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
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
                          cases tail' with
                          | nil =>
                              cases third with
                              | word thirdValue =>
                                  exact hthree context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException left right thirdValue
                                    targetState targetException hcontrol
                              | rStruct fields =>
                                  exact hother context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException
                                    (.rStruct
                                      [.word left, .word right,
                                        .rStruct fields]) targetState targetException
                                    (by
                                      intro value h
                                      nomatch h)
                                    (by
                                      intro left' right' h
                                      have hlen := congrArg
                                        (fun value : PanValue α =>
                                          match value with
                                          | .word _ => 0
                                          | .rStruct values => values.length
                                          | .nStruct _ values => values.length) h
                                      simp at hlen) hcontrol
                              | nStruct name fields =>
                                  exact hother context structs exceptionRel
                                    sourceLocals sourceGlobals sourceMemory
                                    sourceException
                                    (.rStruct
                                      [.word left, .word right,
                                        .nStruct name fields]) targetState targetException
                                    (by
                                      intro value h
                                      nomatch h)
                                    (by
                                      intro left' right' h
                                      have hlen := congrArg
                                        (fun value : PanValue α =>
                                          match value with
                                          | .word _ => 0
                                          | .rStruct values => values.length
                                          | .nStruct _ values => values.length) h
                                      simp at hlen) hcontrol
                          | cons fourth tail'' =>
                              exact hother context structs exceptionRel
                                sourceLocals sourceGlobals sourceMemory
                                sourceException
                                  (.rStruct
                                  (.word left :: .word right :: third ::
                                    fourth :: tail'')) targetState targetException
                                (by
                                  intro value h
                                  nomatch h)
                                (by
                                  intro left' right' h
                                  have hlen := congrArg
                                    (fun value : PanValue α =>
                                      match value with
                                      | .word _ => 0
                                      | .rStruct values => values.length
                                      | .nStruct _ values => values.length) h
                                  simp at hlen) hcontrol
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

theorem panValuePcRaisedHraiseCases_to_exception_result_rel
    [BEq α] [LawfulBEq α]
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
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
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRel structs context exceptionRel exceptionCode
        globalsLookup sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException := by
  intro context structs exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException hcontrol
  exact panValuePcRaisedHraiseData_to_exception_result_rel
    structs context exceptionRel exceptionCode globalsLookup
    (hraiseData context structs exceptionRel)
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    targetState targetException hcontrol

theorem panValuePcRaisedHraiseCases_to_exception_result_rel_with_context_code
    [BEq α] [LawfulBEq α]
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        (.rStruct [.word left, .word right]) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    ∀ (context : CompileContext α) (structs : StructContext)
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
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  have hraiseEvidence := panValuePcRaisedHraiseCases_paired exceptionCode globalsLookup
    hword htwo hthree hother
  exact panValuePcRaisedHraiseData_to_exception_result_rel_with_context_code
    structs context exceptionRel exceptionCode globalsLookup
    (fun sourceLocals sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException hcontrol =>
      hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException hcontrol

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
    (hsafe : panValuePcControlLabelSafe sourceResult crepResult)
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
          have hlabel : targetLabel = 0 := by
            simpa [panValuePcControlLabelSafe] using hsafe
          subst targetLabel
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | continued sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | continued targetState targetLabel =>
          cases hresult
          have hlabel : targetLabel = 0 := by
            simpa [panValuePcControlLabelSafe] using hsafe
          subst targetLabel
          simpa [panValuePcResultOfControl, panValuePcResultRel,
            panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | broke _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol

theorem panValuePcResultRelWithContextCode_of_control
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
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (targetResult : CrepPcResult α)
    (hcontrol : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult)
    (hsafe : panValuePcControlLabelSafe sourceResult crepResult)
    (hresult : crepPcResultOfControl crepResult = some targetResult) :
    panValuePcResultRelWithContextCode structs context exceptionRel
      exceptionCode globalsLookup
      (panValuePcResultOfControl sourceResult) targetResult := by
  cases sourceResult with
  | normal sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | normal targetState =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRelWithContextCode,
            panValuePcResultRel, panValueCrepControlRel] using hcontrol
      | returned _ _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | returned sourceLocals sourceGlobals sourceMemory sourceValues =>
      cases crepResult with
      | returned targetState targetValues =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRelWithContextCode,
            panValuePcResultRel, panValueCrepControlRel] using hcontrol
      | normal _ | raised _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue =>
      cases crepResult with
      | raised targetState targetException =>
          cases hresult
          simpa [panValuePcResultOfControl, panValuePcResultRelWithContextCode] using
            (hraise sourceLocals sourceGlobals sourceMemory sourceException
              sourceValue targetState targetException hcontrol)
      | normal _ | returned _ _ | broke _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | broke sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | broke targetState targetLabel =>
          cases hresult
          have hlabel : targetLabel = 0 := by
            simpa [panValuePcControlLabelSafe] using hsafe
          subst targetLabel
          simpa [panValuePcResultOfControl, panValuePcResultRelWithContextCode,
            panValuePcResultRel, panValueCrepControlRel] using hcontrol
      | normal _ | returned _ _ | raised _ _ | continued _ _ | finalFfi _ _ =>
          simp [panValueCrepControlRel] at hcontrol
  | continued sourceLocals sourceGlobals sourceMemory =>
      cases crepResult with
      | continued targetState targetLabel =>
          cases hresult
          have hlabel : targetLabel = 0 := by
            simpa [panValuePcControlLabelSafe] using hsafe
          subst targetLabel
          simpa [panValuePcResultOfControl, panValuePcResultRelWithContextCode,
            panValuePcResultRel, panValueCrepControlRel] using hcontrol
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode
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
  have hsafe := hprogramSafe context structs sourceFunctions functions
    sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
    hstate hsourceResult hcrepResult
  have hraise := panValuePcRaisedHraiseData_to_exception_result_rel
    structs context exceptionRel exceptionCode globalsLookup
    (hraiseData context structs exceptionRel)
  have hresult := panValuePcResultRel_of_control structs context exceptionRel
    exceptionCode globalsLookup hraise
    sourceResult crepResult targetExecution.result hcontrol hsafe hcrepShape
  simpa [hsourceShape] using hresult

theorem panValuePcCompileCorrectWithContextCode_of_stateful_program
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode sourceEvaluate targetEvaluate
      codeRel excpRel exceptionCode globalsLookup program := by
  intro context structs sourceInput targetInput exceptionRel sourceExecution
    targetExecution hsourceStructs htargetStructs hlocalisedCode
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
  have hsafe := hprogramSafe context structs sourceFunctions functions
    sourceInput.locals sourceInput.globals sourceInput.memory targetInput.state
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel exceptionRel sourceResult crepResult
    hstate hsourceResult hcrepResult
  have hraise : ∀ (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValueCrepStateRel structs context sourceLocals sourceGlobals
        sourceMemory targetState ∧
      panValuePcExceptionResultRelWithContextCode structs context exceptionRel
        exceptionCode globalsLookup sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
    intro sourceLocals sourceGlobals sourceMemory sourceException sourceValue
      targetState targetException hraised
    exact panValuePcRaisedHraiseData_to_exception_result_rel_with_context_code
      structs context exceptionRel exceptionCode globalsLookup
      (fun sourceLocals sourceGlobals sourceMemory sourceException sourceValue
          targetState targetException hcontrol =>
        hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
          sourceMemory sourceException sourceValue targetState targetException hcontrol)
      sourceLocals sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException hraised
  have hresult := panValuePcResultRelWithContextCode_of_control structs context
    exceptionRel exceptionCode globalsLookup hraise
    sourceResult crepResult targetExecution.result hcontrol hsafe hcrepShape
  simpa [hsourceShape] using hresult

/-! Stateful `pc_compile_correct` composition with the raw-word dispatcher.
    This is the direct HOL-boundary entrypoint for evaluator-backed flat
    records; unsupported non-flat payloads remain an explicit hypothesis. -/
theorem panValuePcCompileCorrect_of_stateful_program_with_raw_word_lists
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException) :
    PanValuePcCompileCorrect sourceEvaluate targetEvaluate codeRel excpRel
      exceptionCode globalsLookup program := by
  have hraise := panValuePcRaisedHraiseCases_with_raw_word_lists
    exceptionCode globalsLookup hword hraw hother
  exact panValuePcCompileCorrect_of_stateful_program
    program sourceEvaluate targetEvaluate codeRel excpRel exceptionCode
    globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
    ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
    hprogram hprogramSafe hsourceAdapter htargetAdapter hraise

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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException)
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
    hword htwo hthree hother
  refine panValuePcCompileCorrect_of_stateful_program
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_ ?_ hraise
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval

/-! Compact-evaluator entrypoint retaining the exact Cake exception-code
    lookup in the raised result relation.  The raised-data and lookup facts
    travel together so evaluator-backed semantic slices cannot lose the HOL
    exception provenance at this boundary. -/
theorem panValuePcCompileCorrect_compact_with_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  refine panValuePcCompileCorrectWithContextCode_of_stateful_program
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_ ?_ hraiseEvidence
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval

theorem panValuePcCompileCorrect_compact_with_context_code_cases
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        (.rStruct [.word left, .word right]) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraiseEvidence := panValuePcRaisedHraiseCases_paired exceptionCode globalsLookup
    hword htwo hthree hother
  exact panValuePcCompileCorrect_compact_with_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Compact-evaluator entrypoint using evaluator-backed raw word records.
    The non-flat callback remains explicit, so this convenience theorem does
    not turn unsupported structured payloads into an assumed result. -/
theorem panValuePcCompileCorrect_compact_with_raw_word_lists
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
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
  refine panValuePcCompileCorrect_of_stateful_program_with_raw_word_lists
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_ ?_ hword hraw hother
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval

/-! Compact raw-word entrypoint retaining Cake's exact exception-code lookup.
    Every flat record length uses the canonical global-spill callback; the
    non-flat callback remains explicit. -/
theorem panValuePcCompileCorrect_compact_with_raw_word_lists_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
        (.word value) targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraiseEvidence := panValuePcRaisedHraiseCases_with_raw_word_lists_paired
    exceptionCode globalsLookup hword hraw hother
  exact panValuePcCompileCorrect_compact_with_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Compact context-code boundary for canonical flat-global evidence.  The
    raised callback is proved once against the compiler-owned lookup and is
    retargeted extensionally before entering `pc_compile_correct`. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_callback_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hretargeted :=
    panValuePcRaisedHraiseData_retarget_globals_callback_with_context_code
      bytesInWord exceptionCode globalsLookup hlookup hraiseEvidence
  exact panValuePcCompileCorrect_compact_with_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hretargeted context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Raw-word convenience form of the canonical flat-global boundary.  Word
    and arbitrary flat-record callbacks stay on the compiler lookup, while
    the final theorem exposes the caller's HOL `globalsLookup`. -/
theorem panValuePcCompileCorrect_compact_with_raw_word_flat_globals_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hword : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (value : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException (.word value)
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException ∧
      lookupInfo sourceException context.exceptions = some targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  let hraiseEvidence := panValuePcRaisedHraiseCases_with_raw_word_lists_paired
    exceptionCode (crepPcFlatGlobalsLookup bytesInWord) hword hraw hother
  exact panValuePcCompileCorrect_compact_with_flat_global_callback_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hlookup
    (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Generic evaluator-evidence form of the compact context-code boundary.
    This keeps arbitrary structured payloads on the canonical flattened lookup
    while exposing the exact HOL exception-code relation to callers. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_evidence_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  exact panValuePcCompileCorrect_compact_with_flat_global_callback_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hlookup (by
      exact hraiseEvidence)

/-! Control-only entrypoint with explicit raised evidence.  The control
    relation supplies the spill witness; callers provide the post-state,
    exception-code, canonical lookup, and shape-size facts separately. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_control_evidence_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
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
        panValueCrepRaisedControlRel structs context exceptionRel sourceGlobals
          sourceMemory sourceException sourceValue targetState targetException
          spillAddress ∧
        exceptionCode sourceException = some targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
          crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
            some (panValueFlatWords sourceValue)) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  apply panValuePcCompileCorrect_compact_with_flat_global_evidence_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hlookup
  · intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException hcontrol
    rcases hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException hcontrol with
      ⟨hpost, spillAddress, hraised, hcode, hlookupCode, hpayload, hsize⟩
    exact panValuePcRaisedHraiseData_of_control_evidence_with_context_code
      structs context exceptionRel exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException
      hpost hcontrol hcode hpayload hsize hlookupCode

/-! Ordinary `pc_compile_correct` companion for explicit control evidence.
    This is the same raised payload/global lookup lift without requiring the
    stronger exception-context-code relation. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_control_evidence
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseEvidence : ∀ (context : CompileContext α) (structs : StructContext)
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
        panValueCrepRaisedControlRel structs context exceptionRel sourceGlobals
          sourceMemory sourceException sourceValue targetState targetException
          spillAddress ∧
        exceptionCode sourceException = some targetException ∧
        (1 ≤ Shape.shapeSize (panValueShape structs sourceValue) →
          crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
            some (panValueFlatWords sourceValue)) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32)) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  apply panValuePcCompileCorrect_of_stateful_program
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval
  · intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
      sourceException sourceValue targetState targetException hcontrol
    rcases hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException hcontrol with
      ⟨hpost, spillAddress, hraised, hcode, hpayload, hsize⟩
    have hcanonical := panValuePcRaisedHraiseData_of_control_evidence
      structs context exceptionRel exceptionCode
      (crepPcFlatGlobalsLookup bytesInWord) sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException
      hpost hcontrol hcode hpayload hsize
    exact panValuePcRaisedHraiseData_retarget_globals_lookup bytesInWord
      exceptionCode globalsLookup structs context exceptionRel sourceLocals
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException (hlookup targetState sourceValue) hcanonical

/-! Evidence-bearing compact boundary.  Unlike the case dispatcher above,
this entrypoint accepts generic evaluator/storeGlobals evidence directly, so
arbitrary structured raised payloads are not forced through an opaque
control-only fallback. -/
theorem panValuePcCompileCorrect_compact_with_raised_data
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  refine panValuePcCompileCorrect_of_stateful_program
    program
    (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel)
    (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel)
    codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_ ?_ hraiseData
  · intro context structs sourceInput targetInput sourceExecution hstructs heval
    exact panValuePcCompactSourceEvaluator_adapter primitive sourceHandler
      sourceFunctions baseAddress topAddress bytesInWord sourceFuel program
      context structs sourceInput targetInput sourceExecution hstructs heval
  · intro context structs sourceInput targetInput targetExecution hstructs heval
    exact crepPcCompactTargetEvaluator_adapter functions crepPrimitive ffi
      sharedMem baseAddress topAddress targetFuel program context structs
      sourceInput targetInput targetExecution hstructs heval

/-! Evidence-bearing compact boundary with a canonical flat-global adapter.
    The raised proof can establish the payload observation against the
    compiler's canonical flattened lookup, while callers may expose an
    extensionally equal HOL lookup at the final boundary. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_evidence
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (_context : CompileContext α) (_structs : StructContext)
      (_exceptionRel : ExceptionId → PanValue α → α → Prop)
      (_sourceLocals _sourceGlobals : VarName → Option (PanValue α))
      (_sourceMemory : α → Option (PanValue α)) (_sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (_targetException : α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  apply panValuePcCompileCorrect_compact_with_raised_data
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  exact panValuePcRaisedHraiseData_retarget_globals_lookup bytesInWord
    exceptionCode globalsLookup structs context exceptionRel sourceLocals
    sourceGlobals sourceMemory sourceException sourceValue targetState
    targetException (hlookup context structs exceptionRel sourceLocals
      sourceGlobals sourceMemory sourceException sourceValue targetState
      targetException)
    (hraiseData context structs exceptionRel sourceLocals sourceGlobals
      sourceMemory sourceException sourceValue targetState targetException
      hcontrol)

/-! Convert evaluator-backed raised evidence into the explicit payload package
    consumed by both compact `pc_compile_correct` boundaries. -/
theorem panValuePcRaisedHraiseData_of_flat_global_evaluator_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (sourceFuel : Nat)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState α) (expression : Exp α)
        (compiled : List (CrepExp α)) (shape : Shape) (values : List α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression = some sourceValue ∧
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state baseAddress topAddress compiled =
          some values ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
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
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  rcases hevidence context structs exceptionRel sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hcontrol with
    ⟨state, expression, compiled, shape, values, htarget, hbytesInWord,
      hrel, hsource, hvalid, hcompile, hlength, hcompiled, hnot, hfresh,
      hexception, hlookupCode, hcode, hflat, hdistinct, hsize⟩
  subst targetState
  have hcanonical :=
    panValuePcRaisedGenericHraise_of_evidence_retarget_globals_with_source_locals
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel sourceException targetException
    expression sourceValue compiled shape values exceptionRel exceptionCode
    globalsLookup hlookupCode hrel hsource hvalid hcompile hlength hcompiled hnot
    hfresh hexception hcode hflat hdistinct hsize
    (by simpa [hbytesInWord] using (hlookup _ _))
  exact hcanonical

/-! Compact `pc_compile_correct` with evaluator-backed raised evidence.  The
    evidence callback exposes the source expression and compiled payload, so
    the boundary can prove the raised result rather than receiving an opaque
    `hraiseData` callback. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState α) (expression : Exp α)
        (compiled : List (CrepExp α)) (shape : Shape) (values : List α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression = some sourceValue ∧
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state baseAddress topAddress compiled =
          some values ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraiseEvidence := panValuePcRaisedHraiseData_of_flat_global_evaluator_evidence
    exceptionCode globalsLookup sourceFunctions functions primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord sourceFuel
    hlookup hevidence
  refine panValuePcCompileCorrect_compact_with_raised_data
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  exact (hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hcontrol).1

/-! Context-code companion for the evaluator-backed boundary.  The callback
    retains Cake's exact `lookupInfo` exception-code provenance. -/
theorem panValuePcCompileCorrect_compact_with_flat_global_evaluator_evidence_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (state : CrepState α) (expression : Exp α)
        (compiled : List (CrepExp α)) (shape : Shape) (values : List α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
          baseAddress topAddress bytesInWord expression = some sourceValue ∧
        panValuePayloadWithinLimit structs sourceValue = true ∧
        compileExp context expression = (compiled, shape) ∧
        compiled.length = Shape.shapeSize shape ∧
        evalCrepFullExpsState state baseAddress topAddress compiled =
          some values ∧
        (∀ name ∈ freshNames context compiled.length 1,
          ∀ value ∈ compiled, name ∉ crepExpVars value) ∧
        (∀ name ∈ freshNames context compiled.length 1,
          state.locals name = none) ∧
        exceptionRel sourceException sourceValue targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraiseEvidence := panValuePcRaisedHraiseData_of_flat_global_evaluator_evidence
    exceptionCode globalsLookup sourceFunctions functions primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord sourceFuel
    hlookup hevidence
  exact panValuePcCompileCorrect_compact_with_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Convert direct flat-spill state evidence into the raised package.  This is
    the state-level companion to the evaluator-backed adapter above: it keeps
    payload storage and global lookup explicit without requiring expression
    compilation evidence. -/
theorem panValuePcRaisedHraiseData_of_flat_spill_evidence
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (bytesInWord : α)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (values : List α) (state : CrepState α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        exceptionRel sourceException sourceValue targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  rcases hevidence context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol with
    ⟨values, state, htarget, hbytesInWord, hrel, hexception, hcode,
      hflat, hdistinct, hsize⟩
  subst targetState
  have hcanonical :=
    panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
      structs context exceptionRel exceptionCode sourceLocals sourceGlobals
      sourceMemory sourceException values state context.bytesInWord targetException
      sourceValue hrel hexception hcode hflat hdistinct hsize
  exact panValuePcRaisedHraiseData_retarget_globals_lookup
    context.bytesInWord exceptionCode globalsLookup structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    targetException (by simpa [hbytesInWord] using (hlookup _ _)) hcanonical

/-! Context-code companion for direct flat-spill evidence.  The evaluator
    witness carries Cake's exception lookup together with the payload facts,
    so the raised boundary does not reconstruct that provenance separately. -/
theorem panValuePcRaisedHraiseData_of_flat_spill_evidence_with_context_code
    [BEq α] [LawfulBEq α] [OfNat α 0] [Add α]
    (exceptionCode : ExceptionId → Option α)
    (globalsLookup : CrepState α → PanValue α → Option (List α))
    (bytesInWord : α)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (values : List α) (state : CrepState α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        exceptionRel sourceException sourceValue targetException ∧
        exceptionCode sourceException = some targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        sourceValue targetState targetException ∧
      lookupInfo sourceException context.exceptions = some targetException := by
  intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
    sourceException sourceValue targetState targetException hcontrol
  rcases hevidence context structs exceptionRel sourceLocals sourceGlobals
    sourceMemory sourceException sourceValue targetState targetException hcontrol with
    ⟨values, state, htarget, hbytesInWord, hrel, hexception, hcode,
      hlookupCode, hflat, hdistinct, hsize⟩
  subst targetState
  have hcanonical :=
    panValuePcRaisedHraiseData_of_flat_spill_state_with_source_locals
      structs context exceptionRel exceptionCode sourceLocals sourceGlobals
      sourceMemory sourceException values state context.bytesInWord targetException
      sourceValue hrel hexception hcode hflat hdistinct hsize
  have hretargeted := panValuePcRaisedHraiseData_retarget_globals_lookup
    context.bytesInWord exceptionCode globalsLookup structs context exceptionRel
    sourceLocals sourceGlobals sourceMemory sourceException sourceValue
    { state with globals :=
        updateMemoryListAt state.globals 0 context.bytesInWord values }
    targetException (by simpa [hbytesInWord] using (hlookup _ _)) hcanonical
  exact ⟨hretargeted, hlookupCode⟩

/-! Ordinary compact `pc_compile_correct` entrypoint for direct flat-spill
    evidence.  The target HOL global lookup is retargeted only through the
    supplied extensional equality. -/
theorem panValuePcCompileCorrect_compact_with_flat_spill_evidence
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (values : List α) (state : CrepState α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        exceptionRel sourceException sourceValue targetException ∧
        exceptionCode sourceException = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  refine panValuePcCompileCorrect_compact_with_raised_data
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe ?_
  exact panValuePcRaisedHraiseData_of_flat_spill_evidence
    exceptionCode globalsLookup bytesInWord hlookup hevidence

theorem panValuePcCompileCorrect_compact_with_flat_spill_evidence_context_code
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hevidence : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α))
      (sourceException : ExceptionId) (sourceValue : PanValue α)
      (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException sourceValue)
        (.raised targetState targetException) →
      ∃ (values : List α) (state : CrepState α),
        targetState =
          { state with globals :=
              updateMemoryListAt state.globals 0 context.bytesInWord values } ∧
        context.bytesInWord = bytesInWord ∧
        panValueCrepStateRel structs context sourceLocals sourceGlobals
          sourceMemory state ∧
        exceptionRel sourceException sourceValue targetException ∧
        exceptionCode sourceException = some targetException ∧
        lookupInfo sourceException context.exceptions = some targetException ∧
        panValueFlatWords sourceValue = values ∧
        List.Pairwise (fun left right : α => left ≠ right)
          (storeAddresses (0 : α) context.bytesInWord values.length) ∧
        Shape.shapeSize (panValueShape structs sourceValue) ≤ 32) :
    PanValuePcCompileCorrectWithContextCode
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  have hraiseEvidence :=
    panValuePcRaisedHraiseData_of_flat_spill_evidence_with_context_code
      exceptionCode globalsLookup bytesInWord hlookup hevidence
  exact panValuePcCompileCorrect_compact_with_context_code
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe (by
      intro context structs exceptionRel sourceLocals sourceGlobals sourceMemory
        sourceException sourceValue targetState targetException hcontrol
      exact hraiseEvidence context structs exceptionRel sourceLocals sourceGlobals
        sourceMemory sourceException sourceValue targetState targetException hcontrol)

/-! Compact `pc_compile_correct` entrypoint for case-split raised evidence.
    Each case proves the canonical flattened lookup first; the boundary then
    retargets that evidence to the caller's HOL `globalsLookup`. -/
theorem panValuePcCompileCorrect_compact_with_raw_word_flat_globals
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hlookup : ∀ (targetState : CrepState α) (sourceValue : PanValue α),
      crepPcFlatGlobalsLookup bytesInWord targetState sourceValue =
        globalsLookup targetState sourceValue)
    (hword : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (value : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.word value))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException
        (.word value) targetState targetException)
    (hraw : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (values : List α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct (values.map (fun value => .word value))))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct (values.map (fun value => .word value))) targetState
        targetException)
    (hother : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (sourceValue : PanValue α) (targetState : CrepState α)
      (targetException : α),
      (∀ value : α, sourceValue ≠ .word value) →
      (∀ values : List α,
        sourceValue ≠ .rStruct (values.map (fun value => .word value))) →
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          sourceValue)
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode
        (crepPcFlatGlobalsLookup bytesInWord) structs context exceptionRel
        sourceLocals sourceGlobals sourceMemory sourceException sourceValue
        targetState targetException) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program := by
  apply panValuePcCompileCorrect_compact_with_flat_global_evidence
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe
  · intro _context _structs _exceptionRel _sourceLocals _sourceGlobals
      _sourceMemory _sourceException sourceValue targetState _targetException
    exact hlookup targetState sourceValue
  · exact panValuePcRaisedHraiseCases_with_raw_word_lists
      exceptionCode (crepPcFlatGlobalsLookup bytesInWord) hword hraw hother

/-! Clocked companion for the evidence-bearing boundary.  The raised branch
continues to consume explicit evaluator/storeGlobals evidence, while the
zero-clock Tick Timeout result is composed independently. -/
theorem panValuePcCompileCorrect_compact_with_raised_data_and_timeout
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException)
    (clockStructs : StructContext) (clockPcContext : CompileContext α)
    (clockExceptionRel : ExceptionId → PanValue α → α → Prop)
    (clockContext : PanValueFfiContext α)
    (clockPrimitive : PanPrimitiveHandler α)
    (clockHandler : PanValueStatefulFfiHandler α σ)
    (clockFunctions : List (FunName × List VarName × Prog α))
    (clockBaseAddress clockTopAddress clockBytesInWord : α)
    (clockFuel : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue α))
    (clockMemory : α → Option (PanValue α)) (clockFfi : FfiState σ)
    (clockTargetState : CrepState α)
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      (fun _ => none) clockGlobals clockMemory clockTargetState) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program ∧
    evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi 0 .tick =
      some (.timeout (fun _ => none) clockGlobals clockMemory clockFfi, 0) ∧
    (evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi 0 .tick).map panValueFfiClockResultProjection =
      some (.timeout (fun _ => none) clockGlobals clockMemory clockFfi 0) ∧
    panValuePcResultRel clockStructs clockPcContext clockExceptionRel
      exceptionCode globalsLookup
      (.timeout (fun _ => none) clockGlobals clockMemory)
      (.timeout clockTargetState) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact panValuePcCompileCorrect_compact_with_raised_data program codeRel
      excpRel exceptionCode globalsLookup sourceFunctions functions primitive
      sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
      sourceFuel targetFuel hprogram hprogramSafe hraiseData
  · exact panValuePcTimeoutResultRel_of_clocked_tick_zero clockStructs
      clockPcContext clockExceptionRel exceptionCode globalsLookup clockContext
      clockPrimitive clockHandler clockFunctions clockBaseAddress
      clockTopAddress clockBytesInWord clockFuel clockLocals clockGlobals
      clockMemory clockFfi clockTargetState hclockState |>.1
  · exact panValuePcTimeoutResultRel_of_clocked_tick_zero clockStructs
      clockPcContext clockExceptionRel exceptionCode globalsLookup clockContext
      clockPrimitive clockHandler clockFunctions clockBaseAddress
      clockTopAddress clockBytesInWord clockFuel clockLocals clockGlobals
      clockMemory clockFfi clockTargetState hclockState |>.2.1
  · exact panValuePcTimeoutResultRel_of_clocked_tick_zero clockStructs
      clockPcContext clockExceptionRel exceptionCode globalsLookup clockContext
      clockPrimitive clockHandler clockFunctions clockBaseAddress
      clockTopAddress clockBytesInWord clockFuel clockLocals clockGlobals
      clockMemory clockFfi clockTargetState hclockState |>.2.2

/-! FinalFFI companion for the evidence-bearing compact boundary.  The leaf
evaluator evidence and event equality remain explicit, while the complete
FinalFFI state/event projection is preserved in the Pc relation. -/
theorem panValuePcCompileCorrect_compact_with_raised_data_and_final_ffi
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
    (hraiseData : ∀ (context : CompileContext α) (structs : StructContext)
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
        sourceValue targetState targetException)
    (clockStructs : StructContext) (clockPcContext : CompileContext α)
    (clockExceptionRel : ExceptionId → PanValue α → α → Prop)
    (clockContext : PanValueFfiContext α)
    (clockPrimitive : PanPrimitiveHandler α)
    (clockHandler : PanValueStatefulFfiHandler α σ)
    (clockFunctions : List (FunName × List VarName × Prog α))
    (clockBaseAddress clockTopAddress clockBytesInWord : α)
    (clock : Nat) (clockLocals clockGlobals : VarName → Option (PanValue α))
    (clockMemory : α → Option (PanValue α)) (clockFfi : FfiState σ)
    (clockProgram : Prog α) (clockTargetState : CrepState α)
    (event targetEvent : FfiFinalEvent) (steps : Nat)
    (finalFfi : FfiState σ)
    (hsteps : evalPanValueFfiProgSteps clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord 1 clockLocals clockGlobals clockMemory clockFfi
      clockProgram =
      some (.finalFfi clockLocals clockGlobals clockMemory finalFfi event, steps))
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      clockLocals clockGlobals clockMemory clockTargetState)
    (hevent : event = targetEvent) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program ∧
    evalPanValueFfiClockLeaf clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clock clockLocals clockGlobals clockMemory clockFfi
      clockProgram =
      some (.control
        (.finalFfi clockLocals clockGlobals clockMemory finalFfi event), clock) ∧
    (evalPanValueFfiClockLeaf clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord clock clockLocals clockGlobals clockMemory clockFfi
      clockProgram).map panValueFfiClockResultProjection =
      some (.finalFfi clockLocals clockGlobals clockMemory finalFfi event clock) ∧
    panValuePcResultRel clockStructs clockPcContext clockExceptionRel
      exceptionCode globalsLookup
      (.finalFfi clockLocals clockGlobals clockMemory event)
      (.finalFfi clockTargetState targetEvent) := by
  have hcompact := panValuePcCompileCorrect_compact_with_raised_data
    program codeRel excpRel exceptionCode globalsLookup sourceFunctions functions
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel hprogram hprogramSafe hraiseData
  have hfinal := panValuePcFinalFfiResultRel_of_clocked_leaf
    clockStructs clockPcContext clockExceptionRel exceptionCode globalsLookup
    clockContext clockPrimitive clockHandler clockFunctions clockBaseAddress
    clockTopAddress clockBytesInWord clock clockLocals clockGlobals clockMemory
    clockFfi clockProgram clockTargetState event targetEvent steps finalFfi
    hsteps hclockState hevent
  exact ⟨hcompact, hfinal.1, hfinal.2.1, hfinal.2.2⟩

/-! Assemble the unclocked compact correctness theorem with the clocked
    Timeout branch.  The compact evaluator itself has no timeout constructor,
    so this theorem keeps its `PanValuePcCompileCorrect` conclusion intact
    and packages the exact clocked Timeout/Pc relation alongside it.  No
    timeout premise is added to the unclocked top-level theorem; only the
    target state relation needed by the clocked boundary remains explicit. -/
theorem panValuePcCompileCorrect_compact_with_clocked_timeout
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
    (hprogramSafe : PanValueCrepProgramStateControlSafe program)
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
    (hthree : ∀ (context : CompileContext α) (structs : StructContext)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (sourceLocals sourceGlobals : VarName → Option (PanValue α))
      (sourceMemory : α → Option (PanValue α)) (sourceException : ExceptionId)
      (first second third : α) (targetState : CrepState α) (targetException : α),
      panValueCrepControlRel structs context exceptionRel
        (.raised sourceLocals sourceGlobals sourceMemory sourceException
          (.rStruct [.word first, .word second, .word third]))
        (.raised targetState targetException) →
      panValuePcRaisedHraiseData exceptionCode globalsLookup structs context
        exceptionRel sourceLocals sourceGlobals sourceMemory sourceException
        (.rStruct [.word first, .word second, .word third]) targetState
        targetException)
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
        sourceValue targetState targetException)
    (clockStructs : StructContext) (clockPcContext : CompileContext α)
    (clockExceptionRel : ExceptionId → PanValue α → α → Prop)
    (clockContext : PanValueFfiContext α)
    (clockPrimitive : PanPrimitiveHandler α)
    (clockHandler : PanValueStatefulFfiHandler α σ)
    (clockFunctions : List (FunName × List VarName × Prog α))
    (clockBaseAddress clockTopAddress clockBytesInWord : α)
    (clockFuel : Nat)
    (clockLocals clockGlobals : VarName → Option (PanValue α))
    (clockMemory : α → Option (PanValue α)) (clockFfi : FfiState σ)
    (clockTargetState : CrepState α)
    (hclockState : panValueCrepStateRel clockStructs clockPcContext
      (fun _ => none) clockGlobals clockMemory clockTargetState) :
    PanValuePcCompileCorrect
      (panValuePcCompactSourceEvaluator primitive sourceHandler sourceFunctions
        baseAddress topAddress bytesInWord sourceFuel)
      (crepPcCompactTargetEvaluator functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel)
      codeRel excpRel exceptionCode globalsLookup program ∧
    evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi 0 .tick =
      some (.timeout (fun _ => none) clockGlobals clockMemory clockFfi, 0) ∧
    (evalPanValueFfiClockProg clockContext clockPrimitive clockHandler
      clockStructs clockFunctions clockBaseAddress clockTopAddress
      clockBytesInWord (clockFuel + 1) clockLocals clockGlobals clockMemory
      clockFfi 0 .tick).map panValueFfiClockResultProjection =
      some (.timeout (fun _ => none) clockGlobals clockMemory clockFfi 0) ∧
    panValuePcResultRel clockStructs clockPcContext clockExceptionRel
      exceptionCode globalsLookup
      (.timeout (fun _ => none) clockGlobals clockMemory)
      (.timeout clockTargetState) := by
  refine ⟨?_, ?_⟩
  · exact panValuePcCompileCorrect_compact program codeRel excpRel exceptionCode
      globalsLookup sourceFunctions functions primitive sourceHandler crepPrimitive
      ffi sharedMem baseAddress topAddress bytesInWord sourceFuel targetFuel
      hprogram hprogramSafe hword htwo hthree hother
  · exact panValuePcTimeoutResultRel_of_clocked_tick_zero clockStructs
      clockPcContext clockExceptionRel exceptionCode globalsLookup clockContext
      clockPrimitive clockHandler clockFunctions clockBaseAddress
      clockTopAddress clockBytesInWord clockFuel clockLocals clockGlobals
      clockMemory clockFfi clockTargetState hclockState

end Flapjack
