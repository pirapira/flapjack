import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem

/-!
Constructor-case evaluator equations used by the `pc_compile_correct`
evaluation induction. These are Flapjack proof infrastructure: the HOL script
proves the cases inside `pc_compile_correct` and does not export these Lean
lemmas as standalone declarations.
-/

namespace Flapjack

/-- Flapjack-specific unfolding of the source evaluator for `Skip`, used in
the `pc_compile_correct` induction; HOL has no standalone lemma with this statement. -/
theorem panSkipEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      .skip memoryAccess contracts memoryHandler =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

/-- Flapjack-specific target evaluator unfolding for `Skip`; not a standalone HOL theorem. -/
theorem crepSkipEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state .skip =
      some (.normal, state) := by
  exact evalCrepRuntimeResult_skip handler primitive fuel state

/-- Flapjack-specific unfolding showing that the compiler leaves `Skip` unchanged. -/
theorem compileProgHOL_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) :
    compileProgHOL context .skip = .skip := rfl

/-- Flapjack-specific source evaluator unfolding for `Break`; not a standalone HOL theorem. -/
theorem panBreakEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      .break memoryAccess contracts memoryHandler =
      some (.control (.broke locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

/-- Flapjack-specific source evaluator unfolding for `Continue`; not a standalone HOL theorem. -/
theorem panContinueEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      .continue memoryAccess contracts memoryHandler =
      some (.control (.continued locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

/-- Flapjack-specific source evaluator unfolding for `Annot`; not a standalone HOL theorem. -/
theorem panAnnotEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (tag text : String)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      (.annot tag text) memoryAccess contracts memoryHandler =
      some (.control (.normal locals globals memory ffi), clock) := by
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

/-- Flapjack-specific source evaluator unfolding for `Tick`; not a standalone HOL theorem. -/
theorem panTickEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      .tick memoryAccess contracts memoryHandler =
      if clock = 0 then some (panValueFfiClockTimeout globals memory ffi clock)
      else some (.control (.normal locals globals memory ffi), decPanClock clock) := by
  simp [evalPanValueFfiClockProg, panValueFfiClockTimeout]

/-- Flapjack-specific target evaluator unfolding for `Tick`; not a standalone HOL theorem. -/
theorem crepTickEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state .tick =
      if state.clock = 0 then some (.timeout, clearCrepRuntimeLocals state)
      else some (.normal, decCrepClock state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]

/-- Flapjack-specific target evaluator unfolding for `Break`; not a standalone HOL theorem. -/
theorem crepBreakEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state (.break 0) =
      some (.broke 0, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]

/-- Flapjack-specific target evaluator unfolding for `Continue`; not a standalone HOL theorem. -/
theorem crepContinueEvaluationEquation
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state (.continue 0) =
      some (.continued 0, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]

/-- The compiler's control-flow leaf equations correspond to HOL's
`pc_compile_correct[Break]`, `[Continue]`, `[Annot]`, and `[Tick]` cases. -/
theorem compileProgHOL_controlLeaves
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] (context : PanToCrepHOLContext α)
    (tag text : String) :
    compileProgHOL context .break = .break 0 ∧
    compileProgHOL context .continue = .continue 0 ∧
    compileProgHOL context (.annot tag text) = .skip ∧
    compileProgHOL context .tick = .tick := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The state-owned source evaluator's Skip equation. This uses the actual
`PanSemState.code` boundary and the source state's derived fuel. -/
theorem panSemEvaluateCodeState_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .skip
      (memoryAccess := memoryAccess) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.skip : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.skip : Prog α) with
  | zero => omega
  | succ fuel =>
      simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps]

/-- State-boundary Skip case for the source-run-implies-target-run direction
of HOL `pc_compile_correct`.  Both code relations use the code fields owned
by their real runtime states; the source post-state is `panSemCodeStateAfter`
and the target post-state is the result returned by the Crep evaluator.  This
is local case infrastructure and is deliberately untagged: the complete
`pc_compile_correct` induction and its other constructors remain open. The
target side chooses its own fuel existentially, rather than forcing the source
evaluation's fuel or a fixed cutoff onto the target run. -/
theorem panToCrepPcCompileCorrectSkipCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .skip =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetFuel targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive targetFuel targetState
        (compileCodeRelProg context .skip) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .normal ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hsource := panSemEvaluateCodeState_skip sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  refine ⟨1, .normal, targetState, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp [compileCodeRelProg, compileProgHOL, evalCrepRuntimeResult,
      evalCrepRuntimeProg]
  · simpa [hsourcePost] using hstate
  · simpa [hsourcePost] using hcode
  · simpa [hsourcePost] using hexcp
  · simpa [hsourcePost] using hlocals

/-- The state-owned source evaluator's Break equation. -/
theorem panSemEvaluateCodeState_break
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .break
      (memoryAccess := memoryAccess) =
      some (.control (.broke state.locals state.globals state.memory state.ffi),
        state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.break : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.break : Prog α) with
  | zero => omega
  | succ fuel =>
      simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps]

/-- Actual-state Break case for the source-run-implies-target-run direction of
HOL `pc_compile_correct`. It proves all runtime, code, exception, and local
relations over the code fields carried by the source and target states. This
is local case infrastructure, not the complete theorem. -/
theorem panToCrepPcCompileCorrectBreakCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .break =
        some (.control (.broke sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .break) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.broke sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.broke sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.broke sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .broke 0 ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.broke sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hsource := panSemEvaluateCodeState_break sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.broke sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  refine ⟨.broke 0, targetState, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [compileCodeRelProg, compileProgHOL] using
      (crepBreakEvaluationEquation targetHandler targetPrimitive fuel targetState)
  · simpa [hsourcePost] using hstate
  · simpa [hsourcePost] using hcode
  · simpa [hsourcePost] using hexcp
  · simpa [hsourcePost] using hlocals

/-- The state-owned source evaluator's Continue equation. -/
theorem panSemEvaluateCodeState_continue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .continue
      (memoryAccess := memoryAccess) =
      some (.control (.continued state.locals state.globals state.memory state.ffi),
        state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.continue : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.continue : Prog α) with
  | zero => omega
  | succ fuel =>
      simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps]

/-- Actual-state Continue case for the source-run-implies-target-run direction
of HOL `pc_compile_correct`. It preserves source and target runtime, code, and
exception state and proves the post-state local relation. -/
theorem panToCrepPcCompileCorrectContinueCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .continue =
        some (.control (.continued sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .continue) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.continued sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.continued sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.continued sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .continued 0 ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.continued sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hsource := panSemEvaluateCodeState_continue sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.continued sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  refine ⟨.continued 0, targetState, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [compileCodeRelProg, compileProgHOL] using
      (crepContinueEvaluationEquation targetHandler targetPrimitive fuel targetState)
  · simpa [hsourcePost] using hstate
  · simpa [hsourcePost] using hcode
  · simpa [hsourcePost] using hexcp
  · simpa [hsourcePost] using hlocals

/-- The state-owned source evaluator's Tick equation, including the source
zero-clock timeout and positive-clock decrement. -/
theorem panSemEvaluateCodeState_tick
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .tick
      (memoryAccess := memoryAccess) =
      if state.clock = 0 then
        some (panValueFfiClockTimeout state.globals state.memory state.ffi state.clock)
      else some (.control (.normal state.locals state.globals state.memory state.ffi),
        decPanClock state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.tick : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.tick : Prog α) with
  | zero => omega
  | succ fuel =>
      by_cases hclock : state.clock = 0 <;>
        simp [evalPanValueFfiClockCodeProg, panValueFfiClockTimeout, hclock]

/-- Actual-state Tick case for HOL `pc_compile_correct`. The source and target
run and state relations use the production finite code fields, and the two
clock branches retain the source timeout/decrement behavior. -/
theorem panToCrepPcCompileCorrectTickCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .tick =
        (if sourceState.clock = 0 then
          some (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)
        else some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), decPanClock sourceState.clock)) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .tick) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (if sourceState.clock = 0 then
          panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock
        else (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), decPanClock sourceState.clock)))
        targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (if sourceState.clock = 0 then
            panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock
          else (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (if sourceState.clock = 0 then
            panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock
          else (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).exceptionShapes ∧
      (sourceState.clock = 0 → targetResult = .timeout) ∧
      (sourceState.clock ≠ 0 →
        targetResult = .normal ∧
        localsRel context
          (panSemCodeStateAfter sourceState
            (if sourceState.clock = 0 then
              panValueFfiClockTimeout sourceState.globals sourceState.memory
                sourceState.ffi sourceState.clock
            else (.control (.normal sourceState.locals sourceState.globals
              sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).locals
          targetPost.locals) := by
  have hsource := panSemEvaluateCodeState_tick sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals, hclock,
    hbe, hffi, hbase, htop⟩
  by_cases hzero : sourceState.clock = 0
  · have htargetZero : targetState.clock = 0 := by omega
    refine ⟨.timeout, clearCrepRuntimeLocals targetState, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1)
        targetState .tick = some (.timeout, clearCrepRuntimeLocals targetState)
      rw [crepTickEvaluationEquation]
      simp [htargetZero]
    · simp [stateRel, panSemCodeStateAfter, panValueFfiClockTimeout,
        clearCrepRuntimeLocals, hzero, htargetZero, hmem, hmemaddrs,
        hshared, hstructs, hglobals, hbe, hffi, hbase, htop]
    · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
        clearCrepRuntimeLocals, hzero] using hcode
    · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
        clearCrepRuntimeLocals, hzero] using hexcp
    · intro _
      rfl
    · intro hnonzero
      exact False.elim (hnonzero hzero)
  · have htargetNonzero : targetState.clock ≠ 0 := by omega
    refine ⟨.normal, decCrepClock targetState, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [compileCodeRelProg, compileProgHOL, htargetNonzero,
        decCrepClock] using
        (crepTickEvaluationEquation targetHandler targetPrimitive fuel targetState)
    · simp only [stateRel, panSemCodeStateAfter, decPanClock, decCrepClock,
        if_neg hzero]
      exact ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
        by rw [hclock], hbe, hffi, hbase, htop⟩
    · simpa [panSemCodeStateAfter, decCrepClock, hzero] using hcode
    · simpa [panSemCodeStateAfter, decCrepClock, hzero] using hexcp
    · intro hzero'
      exact False.elim (hzero hzero')
    · intro _
      constructor
      · rfl
      · simpa [panSemCodeStateAfter, decCrepClock, hzero] using hlocals

/-- The state-owned source evaluator's Annot equation. -/
theorem panSemEvaluateCodeState_annot
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (tag text : String) (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.annot tag text) (memoryAccess := memoryAccess) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.annot tag text) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.annot tag text) with
  | zero => omega
  | succ fuel =>
      simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps]

/-- Actual-state Annot case for HOL `pc_compile_correct`. The source annotation
is evaluated against the production source state; HOL compilation erases it
to Skip, and all runtime/code/exception/local relations are preserved. -/
theorem panToCrepPcCompileCorrectAnnotCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (tag text : String)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState (.annot tag text) =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context (.annot tag text)) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .normal ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hsource := panSemEvaluateCodeState_annot sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState tag text (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  refine ⟨.normal, targetState, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [compileCodeRelProg, compileProgHOL] using
      (crepSkipEvaluationEquation targetHandler targetPrimitive fuel targetState)
  · simpa [hsourcePost] using hstate
  · simpa [hsourcePost] using hcode
  · simpa [hsourcePost] using hexcp
  · simpa [hsourcePost] using hlocals

/-! A narrow state-owned Call evaluator fact used by the actual-state Call
timeout simulation case. -/
theorem panSemEvaluateCodeState_call_zero_clock_timeout_of_entry
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function : FunName)
    (hentry : panSemCodeLookup state.code function = some ([], .skip, .one))
    (hclock : state.clock = 0)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.call none function [] : Prog α) (memoryAccess := memoryAccess) =
      some (panValueFfiClockTimeout state.globals state.memory state.ffi state.clock) := by
  have hlookupCall : lookupPanSemCodeCall state.structs state.code function [] =
      some (.skip, .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  have hargs : evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord []
      (memoryAccess := memoryAccess) = some [] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps]
  have hpositive : 0 < panSemCodeEvaluateFuel state
      (.call none function [] : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  have hcallFuel : 0 < panSemCodeEvaluateFuel state
      (.call none function [] : Prog α) - 1 := by
    unfold panSemCodeEvaluateFuel
    rw [hclock]
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.call none function [] : Prog α) with
  | zero => omega
  | succ fuel =>
      have hcallFuel' : 0 < fuel := by omega
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
            hargs, hlookupCall, hclock, panValueFfiClockTimeout]

/-! A bounded successful Call equation for a nonempty state-owned code map.
The callee has no parameters and returns one word constant, so this isolates
the recursive code lookup and source clock transition used by the Call
induction case. -/
theorem panSemEvaluateCodeState_call_return_const_of_entry
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function : FunName) (value : α)
    (hentry : panSemCodeLookup state.code function =
      some ([], .return (.const value), .one))
    (hclock : state.clock ≠ 0)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.call none function [] : Prog α) (memoryAccess := memoryAccess) =
      some (.control (.returned (fun _ => none) state.globals state.memory
        state.ffi [.word value]), decPanClock state.clock) := by
  have hlookupCall : lookupPanSemCodeCall state.structs state.code function [] =
      some (.return (.const value), .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  have hargs : evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord []
      (memoryAccess := memoryAccess) = some [] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps]
  have hcost : 1 ≤ panSemProgFuel (.call none function [] : Prog α) := by
    simp [panSemProgFuel, panSemCallInfoFuel, panSemExpListFuel]
  have hclockPos : 2 ≤ state.clock + 1 := by omega
  have hbodyPos : 2 ≤ max (panSemProgFuel (.call none function [] : Prog α))
      (panSemCodeBodyFuel state.code) + 1 := by
    have hmax : panSemProgFuel (.call none function [] : Prog α) ≤
        max (panSemProgFuel (.call none function [] : Prog α))
          (panSemCodeBodyFuel state.code) := Nat.le_max_left _ _
    have hmaxPos : 1 ≤ max (panSemProgFuel (.call none function [] : Prog α))
        (panSemCodeBodyFuel state.code) := Nat.le_trans hcost hmax
    omega
  have hbound : 4 ≤ panSemCodeEvaluateFuel state
      (.call none function [] : Prog α) := by
    unfold panSemCodeEvaluateFuel
    have hproduct := Nat.mul_le_mul hclockPos hbodyPos
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.call none function [] : Prog α) with
  | zero => omega
  | succ fuel =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases fuel with
          | zero => omega
          | succ fuel =>
              cases fuel with
              | zero => omega
              | succ fuel =>
                  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
                    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
                    evalPanValueExpCounted, evalPanValueExp,
                    panValueShape, panShapeMatches,
                    hargs, hlookupCall, hclock]

/-! The zero-clock Call timeout branch at the production source/target state
boundary. This is a single induction branch, not the general HOL theorem. -/
theorem panToCrepPcCompileCorrectCallTimeoutCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ) (function : FunName)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (_hlocals : localsRel context sourceState.locals targetState.locals)
    (_hlocalized : localisedProg (.call none function [] : Prog α))
    (hentry : panSemCodeLookup sourceState.code function = some ([], .skip, .one))
    (hclock : sourceState.clock = 0) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState (.call none function [] : Prog α) =
        some (panValueFfiClockTimeout sourceState.globals sourceState.memory
          sourceState.ffi sourceState.clock) ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 2) targetState
        (compileCodeRelProg context (.call none function [])) =
          some (.timeout, targetPost) ∧
      stateRel
        (panSemCodeStateAfter sourceState
          (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup
          (panSemCodeStateAfter sourceState
            (panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)).exceptionShapes := by
  have hsource := panSemEvaluateCodeState_call_zero_clock_timeout_of_entry
    sourceContext sourcePrimitive sourceHandler sourceBytesInWord sourceState
    function hentry hclock (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  have hsourceExact : panSemEvaluateCodeStateWithMemoryModel sourceContext
      sourcePrimitive sourceHandler sourceModel sourceBytesInWord sourceState
      (.call none function [] : Prog α) =
        some (panValueFfiClockTimeout sourceState.globals sourceState.memory
          sourceState.ffi sourceState.clock) := by
    simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([], .skip, .one) := by
    change panSemCodeLookup sourceState.code function = some ([], .skip, .one)
    exact hentry
  have hcodeEntry := codeRelImp context (panSemCodeAsLookup sourceState.code)
    targetState.code hcode function [] (.skip : Prog α) .one hsourceLookup
  rcases hcodeEntry with ⟨_hbodyLocalized, _hfunc, htargetLookup⟩
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals, hclockRel,
    hbe, hffi, hbase, htop⟩
  have htargetZero : targetState.clock = 0 := by omega
  have htargetCodeLookup : FLOOKUP targetState.code function = some ([], .skip) := by
    simpa [Shape.shapeSize, ctxtFc, compileCodeRelProg, compileProgHOL] using
      htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [] targetState.code =
      some (.skip, fun _ => none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCodeLookup]
    simp [assignCrepRuntimeLocals]
  have htargetCallRun : evalCrepRuntimeCall targetHandler targetPrimitive
      (fuel + 1) targetState none function [] =
      some (.timeout, clearCrepRuntimeLocals targetState) := by
    simp [evalCrepRuntimeCall, evalCrepRuntimeExps, htargetCallLookup, htargetZero,
      crepRuntimeCallInfoValid, clearCrepRuntimeLocals]
  refine ⟨hsourceExact, clearCrepRuntimeLocals targetState, ?_, ?_, ?_, ?_⟩
  · simpa [evalCrepRuntimeResult, evalCrepRuntimeProg, compileCodeRelProg,
      compileProgHOL, compileArgsHOL] using htargetCallRun
  · simp [stateRel, panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals, hclock, htargetZero, hmem, hmemaddrs,
      hshared, hstructs, hglobals, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals] using hcode
  · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals] using hexcp

/-! A first successful recursive Call case over production source and target
code maps. The code entry returns one constant word, which makes the nested
source and target executions explicit without weakening the state boundary. -/
theorem panToCrepPcCompileCorrectCallReturnConstCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ) (function : FunName) (value : α)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (_hlocals : localsRel context sourceState.locals targetState.locals)
    (_hlocalized : localisedProg (.call none function [] : Prog α))
    (hentry : panSemCodeLookup sourceState.code function =
      some ([], .return (.const value), .one))
    (hclock : sourceState.clock ≠ 0) :
    let sourceResult : PanValueFfiClockResult α σ :=
      (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi [.word value]), decPanClock sourceState.clock)
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState (.call none function [] : Prog α) =
        some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 3 targetState
        (compileCodeRelProg context (.call none function [])) =
          some (.returned [value], targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes := by
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals, hclockRel,
    hbe, hffi, hbase, htop⟩
  let sourceResult : PanValueFfiClockResult α σ :=
    (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
      sourceState.ffi [.word value]), decPanClock sourceState.clock)
  let targetPost : CrepRuntimeState α σ :=
    clearCrepRuntimeLocals (decCrepClock targetState)
  have hsource := panSemEvaluateCodeState_call_return_const_of_entry
    sourceContext sourcePrimitive sourceHandler sourceBytesInWord sourceState
    function value hentry hclock (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  have hsourceExact : panSemEvaluateCodeStateWithMemoryModel sourceContext
      sourcePrimitive sourceHandler sourceModel sourceBytesInWord sourceState
      (.call none function [] : Prog α) = some sourceResult := by
    simpa [panSemEvaluateCodeStateWithMemoryModel, sourceResult] using hsource
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([], .return (.const value), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context (panSemCodeAsLookup sourceState.code)
    targetState.code hcode function [] (.return (.const value) : Prog α) .one hsourceLookup
  rcases hcodeEntry with ⟨_hbodyLocalized, _hfunc, htargetLookup⟩
  have htargetCodeLookup : FLOOKUP targetState.code function =
      some ([], .return [.const value]) := by
    simpa [Shape.shapeSize, ctxtFc, compileCodeRelProg, compileProgHOL,
      compileExpHOL] using htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [] targetState.code =
      some (.return [.const value], fun _ => none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCodeLookup]
    simp [assignCrepRuntimeLocals]
  have htargetNonzero : targetState.clock ≠ 0 := by omega
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 3 targetState
      (compileCodeRelProg context (.call none function [])) =
        some (.returned [value], targetPost) := by
    simp [targetPost, evalCrepRuntimeResult, evalCrepRuntimeProg,
      evalCrepRuntimeCall, evalCrepRuntimeExps, evalCrepRuntimeExp, compileCodeRelProg,
      compileProgHOL, compileArgsHOL, htargetCallLookup, htargetNonzero,
      crepRuntimeCallInfoValid, decCrepClock, fixCrepRuntimeClock,
      crepRuntimeCallerState, clearCrepRuntimeLocals]
  refine ⟨hsourceExact, targetPost, htargetRun, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      clearCrepRuntimeLocals, decCrepClock, decPanClock, hclockRel,
      hmem, hmemaddrs, hshared, hstructs, hglobals, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost,
      clearCrepRuntimeLocals, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult, targetPost,
      clearCrepRuntimeLocals] using hexcp

/-! Concrete RV64 source-call case boundaries.  These specializations close
the generic model/stride parameters with the word type's fixed source memory
model and 8-byte width; callers cannot supply target-state memory metadata as
source semantics.  They remain induction-case support, not standalone HOL
theorem ports. -/

theorem panToCrepPcCompileCorrectCallTimeoutCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64)) (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals)
    (hlocalized : localisedProg (.call none function [] : Prog (RiscV.Word 64)))
    (hentry : panSemCodeLookup sourceState.code function = some ([], .skip, .one))
    (hclock : sourceState.clock = 0) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState (.call none function [] : Prog (RiscV.Word 64)) =
        some (panValueFfiClockTimeout sourceState.globals sourceState.memory
          sourceState.ffi sourceState.clock) ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 2) targetState
        (compileCodeRelProg context (.call none function [])) =
          some (.timeout, targetPost) ∧
      stateRel
        (panSemCodeStateAfter sourceState
          (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup
          (panSemCodeStateAfter sourceState
            (panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)).exceptionShapes := by
  have hgeneric := panToCrepPcCompileCorrectCallTimeoutCodeState
    (context := context)
    (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive fuel
    sourceState targetState function hstate hcode hexcp hlocals hlocalized hentry hclock
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord] using hgeneric

theorem panToCrepPcCompileCorrectCallReturnConstCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ) (function : FunName)
    (value : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals)
    (hlocalized : localisedProg (.call none function [] : Prog (RiscV.Word 64)))
    (hentry : panSemCodeLookup sourceState.code function =
      some ([], .return (.const value), .one))
    (hclock : sourceState.clock ≠ 0) :
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi [.word value]), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState (.call none function [] : Prog (RiscV.Word 64)) =
        some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 3 targetState
        (compileCodeRelProg context (.call none function [])) =
          some (.returned [value], targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes := by
  have hgeneric := panToCrepPcCompileCorrectCallReturnConstCodeState
    (context := context)
    (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
    sourceState targetState function value hstate hcode hexcp hlocals hlocalized hentry hclock
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord] using hgeneric

/-! Direct nonempty-code-map Call equation for a one-word parameter and a
return of that parameter. This is untagged evaluator infrastructure; the
corresponding original HOL observation is `call_code_map_7`. -/
theorem panSemEvaluateCodeState_callReturnParameter_ofEntry
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function : FunName) (value : α)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : state.clock ≠ 0)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.call none function [.const value] : Prog α)
      (memoryAccess := memoryAccess) =
      some (.control (.returned (fun _ => none) state.globals state.memory
        state.ffi [.word value]), decPanClock state.clock) := by
  let program : Prog α := .call none function [.const value]
  have hprogramFuel : panSemProgFuel program = 2 := by
    simp [program, panSemProgFuel, panSemCallInfoFuel,
      panSemExpFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 3 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by
    rw [hprogramFuel]
    omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress bytesInWord
      [.const value] (memoryAccess := memoryAccess) = some [.word value] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
      evalPanValueExp]
  have hcallee : lookupPanSemCodeCall state.structs state.code function
      [.word value] = some
        (.return (.var .local "parameter"), .one,
          fun key => if key == "parameter" then some (.word value) else none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters, panValueShape,
      panShapeMatches]
    all_goals
      funext key
      simp [updatePanValueMap, beq_iff_eq]
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  have hfuelConcrete : panSemCodeEvaluateFuel state
      (.call none function [.const value] : Prog α) = tail + 5 := by
    simpa [program] using hfuel
  rw [hfuelConcrete]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
    panValueShape, panShapeMatches, decPanClock]

theorem panSemEvaluateRiscV64CodeState_callReturnParameter_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : state.clock ≠ 0) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.call none function [.const value] : Prog (RiscV.Word 64)) =
      some (.control (.returned (fun _ => none) state.globals state.memory
        state.ffi [.word value]), decPanClock state.clock) := by
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess] using
      panSemEvaluateCodeState_callReturnParameter_ofEntry context primitive
        handler panSemBitVec64BytesInWord state function value hentry hclock
        (some (panSemBitVec64MemoryAccess state))

theorem panSemEvaluateRiscV64CodeState_callAssignParameter_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function name : FunName) (value oldValue : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hdestination : state.locals name = some (.word oldValue))
    (hclock : state.clock ≠ 0) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.call (some (some (.local, name), none)) function [.const value] :
        Prog (RiscV.Word 64)) =
      some (.control (.normal
        (updatePanValueMap state.locals name (.word value))
        state.globals state.memory state.ffi), decPanClock state.clock) := by
  let program : Prog (RiscV.Word 64) :=
    .call (some (some (.local, name), none)) function [.const value]
  have hprogramFuel : panSemProgFuel program = 2 := by
    simp [program, panSemProgFuel, panSemCallInfoFuel,
      panSemExpFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 3 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by
    rw [hprogramFuel]
    omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
      [.const value] (memoryAccess := some (panValueMemoryAccessOfModel
        panSemBitVec64WordModel state.memaddrs state.sharedMemaddrs state.be)) =
        some [.word value] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
      evalPanValueExp]
  have hcallee : lookupPanSemCodeCall state.structs state.code function
      [.word value] = some
        (.return (.var .local "parameter"), .one,
          fun key => if key == "parameter" then some (.word value) else none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters, panValueShape,
      panShapeMatches]
    all_goals
      funext key
      simp [updatePanValueMap, beq_iff_eq]
  have hassignment : assignPanValueCallResult state.locals state.globals
      (some (.local, name)) [.word value] state.structs =
        some (updatePanValueMap state.locals name (.word value), state.globals) := by
    simp [assignPanValueCallResult, panValueAssignmentValid, hdestination,
      panValueShape, panShapeMatches]
  unfold panSemEvaluateRiscV64CodeState panSemEvaluateCodeStateWithMemoryModel
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  have hfuelConcrete : panSemCodeEvaluateFuel state program = tail + 5 := hfuel
  rw [hfuelConcrete]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
    hassignment, panValueShape, panShapeMatches, decPanClock]


theorem panSemEvaluateRiscV64CodeState_callRaiseOneWordException_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function exception : String) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : state.exceptionShapes exception = some .one)
    (hclock : state.clock ≠ 0) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.call none function [] : Prog (RiscV.Word 64)) =
      some (.control (.raised (fun _ => none) state.globals state.memory
        state.ffi exception (.word value)), decPanClock state.clock) := by
  let program : Prog (RiscV.Word 64) := .call none function []
  have hprogramFuel : panSemProgFuel program = 1 := by
    simp [program, panSemProgFuel, panSemCallInfoFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 2 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
      ([] : List (Exp (RiscV.Word 64)))
      (memoryAccess := some (panValueMemoryAccessOfModel
        panSemBitVec64WordModel state.memaddrs state.sharedMemaddrs state.be)) = some [] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps]
  have hcallee : lookupPanSemCodeCall state.structs state.code function [] =
      some (.raise exception (.const value), .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  unfold panSemEvaluateRiscV64CodeState panSemEvaluateCodeStateWithMemoryModel
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  rw [show panSemCodeEvaluateFuel state program = tail + 5 from hfuel]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    evalPanValueExpCounted, evalPanValueExp, hargs, hcallee,
    hexception, hclock, panValueShape, panShapeMatches, decPanClock]

/-! One-word state-owned Call exception dispatch to a handler that returns its
local. The preexisting local is explicit because HOL's handler path validates
it before replacing it with the payload. -/
theorem panSemEvaluateRiscV64CodeState_callCatchRaiseOneWord_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function exception handlerVariable : String) (oldValue value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : state.exceptionShapes exception = some .one)
    (hhandlerLocal : state.locals handlerVariable = some (.word oldValue))
    (hclock : state.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) :=
      .call (some (none, some (exception, handlerVariable,
        .return (.var .local handlerVariable)))) function []
    panSemEvaluateRiscV64CodeState context primitive handler state program =
      some (.control (.returned (fun _ => none) state.globals state.memory
        state.ffi [.word value]), decPanClock state.clock) := by
  change panSemEvaluateRiscV64CodeState context primitive handler state
      (.call (some (none, some (exception, handlerVariable,
        .return (.var .local handlerVariable)))) function []) = _
  let program : Prog (RiscV.Word 64) :=
    .call (some (none, some (exception, handlerVariable,
      .return (.var .local handlerVariable)))) function []
  have hprogramFuel : 1 ≤ panSemProgFuel program := by
    simp [program, panSemProgFuel, panSemCallInfoFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 2 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
      ([] : List (Exp (RiscV.Word 64)))
      (memoryAccess := some (panValueMemoryAccessOfModel
        panSemBitVec64WordModel state.memaddrs state.sharedMemaddrs state.be)) = some [] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps]
  have hcallee : lookupPanSemCodeCall state.structs state.code function [] =
      some (.raise exception (.const value), .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  unfold panSemEvaluateRiscV64CodeState panSemEvaluateCodeStateWithMemoryModel
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  rw [show panSemCodeEvaluateFuel state program = tail + 5 from hfuel]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hexception,
    hhandlerLocal, hclock, panValueShape, panShapeMatches, panValueAssignmentValid,
    updatePanValueMap, decPanClock]

/-! Fixed-RV64 source Call exception step for an arbitrary state-owned callee
and its recursive body induction hypothesis. Argument evaluation and recursive
body evaluation both derive memory access from the same `PanSemState`; the
callee lookup is directly through `state.code`. This is source-side induction
support only, not a complete `pc_compile_correct` Call case. -/
theorem panSemEvaluateRiscV64CodeCall_catchesRaisedBody_ofState
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (fuel : Nat)
    (function exception handlerVariable : String)
    (arguments : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (returnShape : Shape) (body : Prog (RiscV.Word 64))
    (calleeLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (calleeRaisedLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (calleeGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (calleeMemory : (RiscV.Word 64) → Option (PanValue (RiscV.Word 64)))
    (calleeFfi : FfiState σ) (exceptionValue : PanValue (RiscV.Word 64))
    (calleeClock : Nat) (handlerProgram : Prog (RiscV.Word 64))
    (handlerResult : PanValueFfiClockResult (RiscV.Word 64) σ)
    (harguments : evalPanSemStateExps state arguments = some values)
    (hcallee : lookupPanSemCodeCall state.structs state.code function values =
      some (body, returnShape, calleeLocals))
    (hclock : state.clock ≠ 0)
    (hcalleeBody : evalPanValueFfiClockCodeProg context primitive handler
      state.structs state.code state.exceptionShapes state.baseAddress
      state.topAddress panSemBitVec64BytesInWord fuel calleeLocals state.globals
      state.memory state.ffi (decPanClock state.clock) body
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
      some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory
        calleeFfi exception exceptionValue), calleeClock))
    (hexceptionShape : ∃ shape,
      state.exceptionShapes exception = some shape ∧
      panShapeMatches (panValueShape state.structs exceptionValue) shape = true)
    (hexceptionValid : panValueExceptionValid state.structs none exception
      exceptionValue = true)
    (hpayload : panValuePayloadWithinLimit state.structs exceptionValue = true)
    (hhandlerAssignment : panValueAssignmentValid state.structs state.locals
      (fun _ => none) .local handlerVariable exceptionValue = true)
    (hhandlerContract : panValueHandlerValid state.structs none state.locals
      handlerVariable exceptionValue = true)
    (hhandlerBody : evalPanValueFfiClockCodeProg context primitive handler
      state.structs state.code state.exceptionShapes state.baseAddress
      state.topAddress panSemBitVec64BytesInWord fuel
      (updatePanValueMap state.locals handlerVariable exceptionValue)
      calleeGlobals calleeMemory calleeFfi (min (decPanClock state.clock) calleeClock)
      handlerProgram (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
      some handlerResult) :
    evalPanValueFfiClockCodeCall context primitive handler state.structs state.code
      state.exceptionShapes state.baseAddress state.topAddress
      panSemBitVec64BytesInWord (fuel + 1) state.locals state.globals state.memory
      state.ffi state.clock
      (some (none, some (exception, handlerVariable, handlerProgram))) function
      arguments (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
      some handlerResult := by
  have harguments' : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
      arguments (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
        some values := by
    simpa [evalPanSemStateExps] using harguments
  exact evalPanValueFfiClockCodeCall_catchesRaisedBody context primitive handler
    state.structs state.code state.exceptionShapes state.baseAddress state.topAddress
    panSemBitVec64BytesInWord fuel state.locals state.globals state.memory state.ffi
    state.clock handlerVariable handlerProgram body function exception arguments
    values returnShape calleeLocals calleeGlobals calleeMemory calleeFfi
    exceptionValue calleeClock
    (memoryAccess := some (panSemBitVec64MemoryAccess state)) (contracts := none)
    (memoryHandler := none) handlerResult harguments' hcallee hclock
    calleeRaisedLocals hcalleeBody hexceptionShape hexceptionValid hpayload
    hhandlerAssignment hhandlerContract hhandlerBody


/-! Actual-state fixed-RV64 Call simulation for a nonempty source code map.
The callee's parameter slot and returned body are derived from `code_rel`;
the result remains induction-case infrastructure, not a standalone HOL tag. -/
theorem panToCrepPcCompileCorrectCallReturnParameterCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function : FunName) (value : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (_hlocals : localsRel context sourceState.locals targetState.locals)
    (_hlocalized : localisedProg
      (.call none function [.const value] : Prog (RiscV.Word 64)))
    (hentry : panSemCodeLookup sourceState.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : sourceState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) :=
      .call none function [.const value]
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi [.word value]), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 3 targetState
        (compileCodeRelProg context program) =
          some (.returned [value], targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes := by
  let program : Prog (RiscV.Word 64) := .call none function [.const value]
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
      sourceState.ffi [.word value]), decPanClock sourceState.clock)
  let targetPost := clearCrepRuntimeLocals (decCrepClock targetState)
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
  have hsource : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using
      panSemEvaluateRiscV64CodeState_callReturnParameter_ofEntry
        sourceContext sourcePrimitive sourceHandler sourceState function value
        hentry hclock
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context
    (panSemCodeAsLookup sourceState.code) targetState.code hcode function
    [("parameter", .one)] (.return (.var .local "parameter")) .one hsourceLookup
  rcases hcodeEntry with ⟨_hbodyLocalized, _hfunc, htargetLookup⟩
  have htargetCodeLookup : FLOOKUP targetState.code function =
      some ([0], .return [.var 0]) := by
    simpa [Shape.shapeSize, ctxtFc, withShape, FUPDATE_LIST, FUPDATE,
      FLOOKUP_update, compileCodeRelProg, compileProgHOL, compileExpHOL] using
        htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [value]
      targetState.code =
        some (.return [.var 0], fun key =>
          if key == 0 then some (.word value) else none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCodeLookup]
    simp [assignCrepRuntimeLocals]
    constructor
    · rfl
    · funext key
      by_cases hkey : key = 0
      · simp [updateCrepRuntimeLocal, hkey]
      · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
        simp [updateCrepRuntimeLocal, hzero, hkey]
  have htargetClock : targetState.clock ≠ 0 := by omega
  have hcompiled : compileCodeRelProg context program =
      .call none function [.const value] := by
    simp [program, compileCodeRelProg, compileProgHOL, compileArgsHOL,
      compileExpHOL]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 3
      targetState (compileCodeRelProg context program) =
        some (.returned [value], targetPost) := by
    simp [targetPost, hcompiled, evalCrepRuntimeResult, evalCrepRuntimeProg,
      evalCrepRuntimeCall, evalCrepRuntimeExps, evalCrepRuntimeExp,
      htargetCallLookup, htargetClock, crepRuntimeCallInfoValid,
      decCrepClock, fixCrepRuntimeClock, crepRuntimeCallerState,
      clearCrepRuntimeLocals, panTheWord]
  refine ⟨hsource, targetPost, htargetRun, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      clearCrepRuntimeLocals, decCrepClock, decPanClock, hclockRel,
      hmem, hmemaddrs, hshared, hstructs, hglobals, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost,
      clearCrepRuntimeLocals, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp

/-! Actual-state fixed-RV64 Call simulation for an existing local destination.
The destination slot comes from the related proof context, while the callee
body and parameter slot come from code_rel. This remains untagged induction
support. -/
theorem panToCrepPcCompileCorrectCallAssignParameterCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function name : FunName) (value oldValue : RiscV.Word 64)
    (targetSlot : Nat)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals)
    (_hlocalized : localisedProg
      (.call (some (some (.local, name), none)) function [.const value] :
        Prog (RiscV.Word 64)))
    (hdestination : sourceState.locals name = some (.word oldValue))
    (hcontextDestination : FLOOKUP context.vars name = some (.one, [targetSlot]))
    (hentry : panSemCodeLookup sourceState.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : sourceState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) :=
      .call (some (some (.local, name), none)) function [.const value]
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.normal (updatePanValueMap sourceState.locals name (.word value))
        sourceState.globals sourceState.memory sourceState.ffi),
        decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 3 targetState
        (compileCodeRelProg context program) = some (.normal, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      localsRel context
        (panSemCodeStateAfter sourceState sourceResult).locals targetPost.locals ∧
      decPanClock sourceState.clock = targetPost.clock := by
  let program : Prog (RiscV.Word 64) :=
    .call (some (some (.local, name), none)) function [.const value]
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.normal (updatePanValueMap sourceState.locals name (.word value))
      sourceState.globals sourceState.memory sourceState.ffi),
      decPanClock sourceState.clock)
  let targetLocals := updateCrepRuntimeLocal targetState.locals targetSlot (.word value)
  let targetPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetState with locals := targetLocals }
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
  have hsource : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using
      panSemEvaluateRiscV64CodeState_callAssignParameter_ofEntry
        sourceContext sourcePrimitive sourceHandler sourceState function name
        value oldValue hentry hdestination hclock
  have hsourceDestinationLookup : FLOOKUP sourceState.locals name =
      some (.word oldValue) := by
    simpa [FLOOKUP] using hdestination
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context
    (panSemCodeAsLookup sourceState.code) targetState.code hcode function
    [("parameter", .one)] (.return (.var .local "parameter")) .one hsourceLookup
  rcases hcodeEntry with ⟨_hbodyLocalized, _hfunc, htargetLookup⟩
  have htargetCodeLookup : FLOOKUP targetState.code function =
      some ([0], .return [.var 0]) := by
    simpa [Shape.shapeSize, ctxtFc, withShape, FUPDATE_LIST, FUPDATE,
      FLOOKUP_update, compileCodeRelProg, compileProgHOL, compileExpHOL] using
        htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [value]
      targetState.code =
        some (.return [.var 0], fun key =>
          if key == 0 then some (.word value) else none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCodeLookup]
    simp [assignCrepRuntimeLocals]
    constructor
    · rfl
    · funext key
      by_cases hkey : key = 0
      · simp [updateCrepRuntimeLocal, hkey]
      · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
        simp [updateCrepRuntimeLocal, hzero, hkey]
  obtain ⟨slots, hsourceContextSlots, hslotLength, hsourceWords, _hwf⟩ :=
    localsRelLookupCtxt context sourceState.locals targetState.locals name
      (.word oldValue) hlocals (by simpa [FLOOKUP] using hdestination)
  have hslots : slots = [targetSlot] := by
    have hpairs : (panValueShape [] (.word oldValue), slots) =
        (.one, [targetSlot]) := by
      apply Option.some.inj
      rw [← hsourceContextSlots, hcontextDestination]
    exact congrArg Prod.snd hpairs
  have htargetOld : targetState.locals targetSlot = some (.word oldValue) := by
    have hmapProp := (optMmapEqSome slots (FLOOKUP targetState.locals)
      ((panValueFlatten (.word oldValue)).map PanWordLab.word)).mp hsourceWords
    rw [hslots] at hmapProp
    simpa [panValueFlatten, FLOOKUP] using hmapProp
  have hcallNames : ([targetSlot].eraseDups).length = 1 := by
    simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  have htargetCallAssign : crepRuntimeAssignExisting targetState.locals
      [targetSlot] [value] = some targetLocals := by
    simp [targetLocals, crepRuntimeAssignExisting, htargetOld, hcallNames]
  have hcallInfo : crepRuntimeCallInfoValid
      (some ([targetSlot], none) : Option (List Nat ×
        Option ((RiscV.Word 64) × CrepProg (RiscV.Word 64)))) = true := by
    simp [crepRuntimeCallInfoValid, hcallNames]
  have htargetClock : targetState.clock ≠ 0 := by omega
  have hcompiled : compileCodeRelProg context program =
      .call (some ([targetSlot], none)) function [.const value] := by
    simp [program, compileCodeRelProg, compileProgHOL, compileArgsHOL,
      compileExpHOL, callDestinationNamesHOL, wrapRt, hcontextDestination]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 3
      targetState (compileCodeRelProg context program) =
        some (.normal, targetPost) := by
    simp [targetPost, targetLocals, hcompiled, evalCrepRuntimeResult,
      evalCrepRuntimeProg, evalCrepRuntimeCall, evalCrepRuntimeExps,
      evalCrepRuntimeExp, htargetCallLookup, htargetCallAssign,
      hcallInfo, htargetClock, decCrepClock,
      fixCrepRuntimeClock, crepRuntimeCallerState,
      clearCrepRuntimeLocals, panTheWord]
  have hlocalsPost : localsRel context
      (updatePanValueMap sourceState.locals name (.word value)) targetLocals := by
    have hupdated := localRelLeZipUpdatePreserved context sourceState.locals
      targetState.locals name (.word oldValue) (.word value) .one [targetSlot]
      hlocals hsourceDestinationLookup hcontextDestination
      (by simp [panValueShape]) (by simp)
    have hsourceMap : FUPDATE sourceState.locals (name, .word value) =
        updatePanValueMap sourceState.locals name (.word value) := by
      funext key
      by_cases hkey : name = key
      · subst key
        simp [FUPDATE, updatePanValueMap]
      · have hforward : (name == key) = false :=
          beq_eq_false_iff_ne.mpr hkey
        have hbackward : (key == name) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm hkey)
        simp [FUPDATE, updatePanValueMap, hforward, hbackward]
    have htargetListMap : FUPDATE_LIST targetState.locals
        ([targetSlot].zip ((panValueFlatten (.word value)).map PanWordLab.word)) =
        updateCrepRuntimeLocal targetState.locals targetSlot (.word value) := by
      calc
        FUPDATE_LIST targetState.locals
            ([targetSlot].zip ((panValueFlatten (.word value)).map PanWordLab.word)) =
              FUPDATE targetState.locals (targetSlot, .word value) := by
                simp [FUPDATE_LIST, panValueFlatten]
        _ = updateCrepRuntimeLocal targetState.locals targetSlot (.word value) := by
          funext key
          by_cases hkey : targetSlot = key
          · subst key
            simp [FUPDATE, updateCrepRuntimeLocal]
          · have hforward : (targetSlot == key) = false :=
              beq_eq_false_iff_ne.mpr hkey
            simp [FUPDATE, updateCrepRuntimeLocal, hforward]
    rw [hsourceMap, htargetListMap] at hupdated
    simpa [targetLocals] using hupdated
  refine ⟨hsource, targetPost, htargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      decCrepClock, decPanClock, hmem, hmemaddrs, hshared, hstructs,
      hglobals, hclockRel, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hlocalsPost
  · simp [targetPost, decPanClock, decCrepClock, hclockRel]

theorem panToCrepPcCompileCorrectSkipCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState .skip =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetFuel targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive targetFuel targetState
        (compileCodeRelProg context .skip) = some (targetResult, targetPost) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧ targetResult = .normal ∧
      localsRel context sourceState.locals targetPost.locals := by
  have hgeneric := panToCrepPcCompileCorrectSkipCodeState
    (context := context) (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
    sourceState targetState hstate hcode hexcp hlocals
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    hsourcePost] using hgeneric

theorem panToCrepPcCompileCorrectBreakCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64)) (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState .break =
        some (.control (.broke sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .break) = some (targetResult, targetPost) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧ targetResult = .broke 0 ∧
      localsRel context sourceState.locals targetPost.locals := by
  have hgeneric := panToCrepPcCompileCorrectBreakCodeState
    (context := context) (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive fuel
    sourceState targetState hstate hcode hexcp hlocals
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.broke sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    hsourcePost] using hgeneric

theorem panToCrepPcCompileCorrectContinueCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64)) (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState .continue =
        some (.control (.continued sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .continue) = some (targetResult, targetPost) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧ targetResult = .continued 0 ∧
      localsRel context sourceState.locals targetPost.locals := by
  have hgeneric := panToCrepPcCompileCorrectContinueCodeState
    (context := context) (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive fuel
    sourceState targetState hstate hcode hexcp hlocals
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.continued sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    hsourcePost] using hgeneric

theorem panToCrepPcCompileCorrectTickCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64)) (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState .tick =
        (if sourceState.clock = 0 then
          some (panValueFfiClockTimeout sourceState.globals sourceState.memory
            sourceState.ffi sourceState.clock)
        else some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), decPanClock sourceState.clock)) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context .tick) = some (targetResult, targetPost) ∧
      stateRel
        (panSemCodeStateAfter sourceState
          (if sourceState.clock = 0 then
            panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock
          else (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), decPanClock sourceState.clock)))
        targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (if sourceState.clock = 0 then
            panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock
          else (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (if sourceState.clock = 0 then
            panValueFfiClockTimeout sourceState.globals sourceState.memory
              sourceState.ffi sourceState.clock
          else (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).exceptionShapes ∧
      (sourceState.clock = 0 → targetResult = .timeout) ∧
      (sourceState.clock ≠ 0 → targetResult = .normal ∧
        localsRel context
          (panSemCodeStateAfter sourceState
            (if sourceState.clock = 0 then
              panValueFfiClockTimeout sourceState.globals sourceState.memory
                sourceState.ffi sourceState.clock
            else (.control (.normal sourceState.locals sourceState.globals
              sourceState.memory sourceState.ffi), decPanClock sourceState.clock))).locals
          targetPost.locals) := by
  have hgeneric := panToCrepPcCompileCorrectTickCodeState
    (context := context) (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive fuel
    sourceState targetState hstate hcode hexcp hlocals
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord] using hgeneric

theorem panToCrepPcCompileCorrectAnnotCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64)) (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ) (tag text : String)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState (.annot tag text) =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetState
        (compileCodeRelProg context (.annot tag text)) = some (targetResult, targetPost) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧ targetResult = .normal ∧
      localsRel context sourceState.locals targetPost.locals := by
  have hgeneric := panToCrepPcCompileCorrectAnnotCodeState
    (context := context) (sourceModel := panSemBitVec64WordModel)
    (sourceBytesInWord := panSemBitVec64BytesInWord)
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive fuel
    sourceState targetState tag text hstate hcode hexcp hlocals
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    hsourcePost] using hgeneric

/-! Direct nonempty-code-map DecCall equation used by the corresponding
actual-state simulation case. This remains untagged proof infrastructure; the
HOL oracle is `deccall_code_map_7` in `pan_sem_e2e_probe.out`. -/
theorem panSemEvaluateCodeState_decCallSkip_ofEntry
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function name : FunName) (value : α)
    (hentry : panSemCodeLookup state.code function =
      some ([("parameter", .one)],
        .return (.var .local "parameter"), .one))
    (hclock : state.clock ≠ 0)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.decCall name .one function [.const value]
        .skip : Prog α) (memoryAccess := memoryAccess) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        decPanClock state.clock) := by
  let program : Prog α :=
    .decCall name .one function [.const value]
      .skip
  have hprogramFuel : panSemProgFuel program = 3 := by
    simp [program, panSemProgFuel, panSemExpFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 4 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by
    rw [hprogramFuel]
    omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress
      bytesInWord [.const value] (memoryAccess := memoryAccess) =
        some [.word value] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps,
      evalPanValueExp]
  have hcallee : lookupPanSemCodeCall state.structs state.code function
      [.word value] = some
        (.return (.var .local "parameter"), .one,
          fun key => if (key == "parameter") then some (.word value) else none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters, panValueShape,
      panShapeMatches]
    all_goals
      funext key
      simp [updatePanValueMap, beq_iff_eq]
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  have hfuelConcrete : panSemCodeEvaluateFuel state
      (.decCall name .one function [.const value]
        .skip : Prog α) = tail + 5 := by
    simpa [program] using hfuel
  rw [hfuelConcrete]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
    panValueShape, panShapeMatches, panValueFfiClockRestoreLocal,
    panValueExpStepCost, restorePanValueFfiLocal, decPanClock]
  all_goals
    funext key
    by_cases hkey : key = name
    · simp [restorePanValueLocal, hkey]
    · simp [restorePanValueLocal, updatePanValueMap, beq_iff_eq, hkey]

theorem panSemEvaluateRiscV64CodeState_decCallSkip_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function name : FunName) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : state.clock ≠ 0) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.decCall name .one function [.const value] .skip : Prog (RiscV.Word 64)) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        decPanClock state.clock) := by
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess] using
      panSemEvaluateCodeState_decCallSkip_ofEntry context primitive handler
        panSemBitVec64BytesInWord state function name value hentry hclock
        (some (panSemBitVec64MemoryAccess state))

/-! Actual-state fixed-RV64 DecCall simulation slice for one word parameter.
The callee's parameter slot and body are obtained from `code_rel`; the
compiled DecCall uses the same state-related target code map and its scoped
target local is restored by the continuation. This remains an induction case,
not a tag on the full `pc_compile_correct` theorem. -/
theorem panToCrepPcCompileCorrectDecCallWordSkipCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function name : FunName) (value : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals)
    (hentry : panSemCodeLookup sourceState.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : sourceState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) :=
      .decCall name .one function [.const value] .skip
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 5 targetState
        (compileCodeRelProg context program) = some (.normal, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      localsRel context
        (panSemCodeStateAfter sourceState sourceResult).locals targetPost.locals ∧
      decPanClock sourceState.clock = targetPost.clock := by
  let program : Prog (RiscV.Word 64) :=
    .decCall name .one function [.const value] .skip
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.normal sourceState.locals sourceState.globals
      sourceState.memory sourceState.ffi), decPanClock sourceState.clock)
  let targetSlot := context.vmax + 1
  let targetPost : CrepRuntimeState (RiscV.Word 64) σ :=
    decCrepClock targetState
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
  have hsource : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using
      panSemEvaluateRiscV64CodeState_decCallSkip_ofEntry sourceContext
        sourcePrimitive sourceHandler sourceState function name value hentry hclock
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context
    (panSemCodeAsLookup sourceState.code) targetState.code hcode function
    [ ("parameter", .one) ] (.return (.var .local "parameter")) .one hsourceLookup
  rcases hcodeEntry with ⟨_hbodyLocalized, _hfunc, htargetLookup⟩
  have htargetCodeLookup : FLOOKUP targetState.code function =
      some ([0], .return [.var 0]) := by
    simpa [Shape.shapeSize, ctxtFc, withShape, FUPDATE_LIST, FUPDATE,
      FLOOKUP_update, compileCodeRelProg, compileProgHOL, compileExpHOL] using htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [value] targetState.code =
      some (.return [.var 0], fun key =>
        if key == 0 then some (.word value) else none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCodeLookup]
    simp [assignCrepRuntimeLocals]
    constructor
    · rfl
    · funext key
      by_cases hkey : key = 0
      · simp [updateCrepRuntimeLocal, hkey]
      · have hzero : (0 == key) = false := by
          simp [Ne.symm hkey]
        simp [updateCrepRuntimeLocal, hzero, hkey]
  have htargetClock : targetState.clock ≠ 0 := by omega
  have hcompiled : compileCodeRelProg context program =
      .dec targetSlot (.const 0)
        (.seq (.call (some ([targetSlot], none)) function [.const value]) .skip) := by
    simp [program, targetSlot, compileCodeRelProg, compileProgHOL,
      allocatedNamesHOL, compileArgsHOL, compileExpHOL, nestedDecs]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 5
      targetState (compileCodeRelProg context program) = some (.normal, targetPost) := by
    have hcallNames : ([targetSlot].eraseDups).length = 1 := by
      simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
    have hcallInfo : crepRuntimeCallInfoValid
        (some ([targetSlot], none) : Option (List Nat ×
          Option ((RiscV.Word 64) × CrepProg (RiscV.Word 64)))) = true := by
      simp [crepRuntimeCallInfoValid, hcallNames]
    simp [targetPost, hcompiled, evalCrepRuntimeResult,
      evalCrepRuntimeProg, evalCrepRuntimeCall, evalCrepRuntimeExp,
      evalCrepRuntimeExps, htargetCallLookup, htargetClock,
      hcallInfo, hcallNames,
      crepRuntimeAssignExisting, updateCrepRuntimeLocal,
      restoreCrepRuntimeStep, clearCrepRuntimeLocals,
      decCrepClock, fixCrepRuntimeClock, crepRuntimeCallerState]
    funext candidate
    by_cases hcandidate : targetSlot = candidate <;> simp [hcandidate]
  refine ⟨hsource, targetPost, htargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      decCrepClock, decPanClock, hmem, hmemaddrs, hshared, hstructs,
      hglobals, hclockRel, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hlocals
  · simp [targetPost, decPanClock, decCrepClock, hclockRel]

/-! Actual-state Call exception propagation with a one-word payload. The
source code entry and compiled target entry are obtained from `code_rel`; the
target exception code comes from the context's exception map, and the payload
is observed through the HOL `globals_lookup` boundary. -/
/-! Executing HOL `exp_hdl` for an existing one-word handler local. The
exception payload is read from the target return-global cell and overwrites
the handler's preexisting local slot, matching the source `set_var` update. -/
theorem crepRuntimeExpHdlOneWord
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (slot : Nat) (value : RiscV.Word 64)
    (hvariable : FLOOKUP variables name = some (Shape.one, [slot]))
    (hslot : ∃ old, state.locals slot = some old)
    (hglobal : state.globals (0 : BitVec 5) = some (.word value)) :
    evalCrepRuntimeProg handler primitive 3 state
      (expHdlFiniteMap variables name) =
        some (.normal,
          { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }) := by
  obtain ⟨old, hslot⟩ := hslot
  have hsetup : expHdlFiniteMap (α := RiscV.Word 64) variables name =
      (.seq (.assign slot (.loadGlob (0 : BitVec 5))) .skip : CrepProg (RiscV.Word 64)) := by
    simp [expHdlFiniteMap, hvariable, loadGlobals, panMap2, crepNestedSeq]
  rw [hsetup]
  simp only [evalCrepRuntimeProg, evalCrepRuntimeExp]
  rw [hglobal]
  simp [hslot, panTheWord, fixCrepRuntimeClock]

/-- The one-word `exp_hdl` execution above yields the `locals_rel` precondition
for the matching source handler body. This is induction support for
`pc_compile_correct[Call_Ret_Exception]`, not a standalone HOL declaration. -/
theorem crepRuntimeExpHdlOneWord_localsRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (sourceLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (name : String) (slot : Nat) (old : PanValue (RiscV.Word 64))
    (value : RiscV.Word 64)
    (hlocals : localsRel context sourceLocals state.locals)
    (hsource : FLOOKUP sourceLocals name = some old)
    (hvariable : FLOOKUP context.vars name = some (Shape.one, [slot]))
    (hslot : ∃ current, state.locals slot = some current)
    (hglobal : state.globals (0 : BitVec 5) = some (.word value)) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive 3 state
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      localsRel context (FUPDATE sourceLocals (name, .word value))
        targetPost.locals := by
  obtain ⟨oldSlots, hcontextOld, _, _, _⟩ :=
    localsRelLookupCtxt context sourceLocals state.locals name old hlocals hsource
  have hshapePair : (panValueShape [] old, oldSlots) = (Shape.one, [slot]) := by
    exact Option.some.inj (hcontextOld.symm.trans hvariable)
  have hshape : panValueShape [] old = panValueShape [] (.word value) := by
    calc
      panValueShape [] old = Shape.one := by
        simpa using congrArg Prod.fst hshapePair
      _ = panValueShape [] (.word value) := by simp [panValueShape]
  obtain ⟨payloadSlots, hcontextPayload, hdistinct, hlocalsPayload⟩ :=
    localsRelUpdateExistingValue context sourceLocals state.locals name old
      (.word value) hlocals hsource hshape
  have hpayloadSlots : payloadSlots = [slot] := by
    have hpairs : (panValueShape [] (.word value), payloadSlots) = (Shape.one, [slot]) :=
      Option.some.inj (hcontextPayload.symm.trans hvariable)
    exact congrArg Prod.snd hpairs
  refine ⟨{ state with locals := updateCrepRuntimeLocal state.locals slot (.word value) },
    ?_, ?_⟩
  · exact crepRuntimeExpHdlOneWord handler primitive state context.vars name slot value
      hvariable hslot hglobal
  · have htargetLocals :
        updateCrepRuntimeLocal state.locals slot (.word value) =
          FUPDATE state.locals (slot, .word value) := by
      funext key
      simp [updateCrepRuntimeLocal, FUPDATE, beq_iff_eq]
    rw [htargetLocals]
    simpa [hpayloadSlots, panValueShape, panValueFlatten, FUPDATE_LIST,
      FUPDATE, beq_iff_eq] using hlocalsPayload

/-! Assemble the one-word `exp_hdl` step with the relations at the matching
source handler entry. The source state contributes its callee post-state, but
its locals are restored from the caller and then assigned the payload; the
target does the same restoration through `crepRuntimeCallerState` before
executing `exp_hdl`. This yields the state, code, exception, and locals
relations expected by a handler-body IH. The callee post-state and payload
global still have to come from the recursive Call IHs. -/
theorem crepRuntimeExpHdlOneWord_handlerPrestateRelations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceCallerLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (targetCaller targetCallee : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (slot : Nat) (old : PanValue (RiscV.Word 64))
    (value : RiscV.Word 64)
    (hstate : stateRel sourceAfterCallee targetCallee)
    (hcode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      targetCallee.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context sourceCallerLocals targetCaller.locals)
    (hsource : FLOOKUP sourceCallerLocals name = some old)
    (hvariable : FLOOKUP context.vars name = some (Shape.one, [slot]))
    (hslot : ∃ current, targetCaller.locals slot = some current)
    (hglobal : targetCallee.globals (0 : BitVec 5) = some (.word value)) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive 3
        (crepRuntimeCallerState targetCaller targetCallee)
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap sourceCallerLocals name (.word value) }
      targetPost ∧
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      localsRel context
        (updatePanValueMap sourceCallerLocals name (.word value)) targetPost.locals := by
  let targetHandlerStart := crepRuntimeCallerState targetCaller targetCallee
  obtain ⟨targetPost, hrun, hlocalsPost⟩ :=
    crepRuntimeExpHdlOneWord_localsRel context handler primitive
      targetHandlerStart sourceCallerLocals name slot old value hlocals hsource
      hvariable hslot hglobal
  have hrunExact := crepRuntimeExpHdlOneWord handler primitive targetHandlerStart
    context.vars name slot value hvariable hslot hglobal
  have hpostPair := Option.some.inj (hrun.symm.trans hrunExact)
  have hpost : targetPost =
      { targetHandlerStart with
        locals := updateCrepRuntimeLocal targetHandlerStart.locals slot (.word value) } :=
    congrArg Prod.snd hpostPair
  have hsourceUpdate : FUPDATE sourceCallerLocals (name, .word value) =
      updatePanValueMap sourceCallerLocals name (.word value) := by
    funext key
    by_cases hkey : name = key
    · subst key
      simp [FUPDATE, updatePanValueMap]
    · have hforward : (name == key) = false :=
        beq_eq_false_iff_ne.mpr hkey
      have hbackward : (key == name) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm hkey)
      simp [FUPDATE, updatePanValueMap, hforward, hbackward]
  refine ⟨targetPost, hrun, ?_, ?_, hexcp, ?_⟩
  · rw [hpost]
    simpa [stateRel, targetHandlerStart, crepRuntimeCallerState] using hstate
  · rw [hpost]
    simpa [targetHandlerStart, crepRuntimeCallerState] using hcode
  · rw [← hsourceUpdate]
    exact hlocalsPost

/-! Execute the compiled matching handler continuation through its Return.
This is the target-side handler-body IH shape used by the actual Call case. -/
theorem crepRuntimeExpHdlReturnOneWord
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (slot : Nat) (value : RiscV.Word 64)
    (hvariable : FLOOKUP variables name = some (Shape.one, [slot]))
    (hslot : ∃ old, state.locals slot = some old)
    (hglobal : state.globals (0 : BitVec 5) = some (.word value)) :
    evalCrepRuntimeProg handler primitive 4 state
      (.seq (expHdlFiniteMap variables name) (.return [.var slot])) =
      some (.returned [value],
        clearCrepRuntimeLocals
          { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }) := by
  have hsetup := crepRuntimeExpHdlOneWord handler primitive state variables
    name slot value hvariable hslot hglobal
  simp only [evalCrepRuntimeProg]
  rw [hsetup]
  simp [evalCrepRuntimeExps, evalCrepRuntimeExp, updateCrepRuntimeLocal,
    panTheWord, clearCrepRuntimeLocals, fixCrepRuntimeClock]

private theorem evalCrepRuntimeExps_vars_eq
    (state : CrepRuntimeState (RiscV.Word 64) σ) (slots : List Nat) :
    evalCrepRuntimeExps state (slots.map CrepExp.var) =
      slots.mapM (fun slot => (state.locals slot).map panTheWord) := by
  induction slots with
  | nil => simp [evalCrepRuntimeExps]
  | cons slot slots ih =>
      simp [evalCrepRuntimeExps, evalCrepRuntimeExp, ih]

private theorem evalCrepRuntimeExps_append
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (left right : List (CrepExp (RiscV.Word 64)))
    (leftValues rightValues : List (RiscV.Word 64))
    (hleft : evalCrepRuntimeExps state left = some leftValues)
    (hright : evalCrepRuntimeExps state right = some rightValues) :
    evalCrepRuntimeExps state (left ++ right) = some (leftValues ++ rightValues) := by
  induction left generalizing leftValues with
  | nil =>
      simp [evalCrepRuntimeExps] at hleft
      subst leftValues
      simpa [evalCrepRuntimeExps] using hright
  | cons expression expressions ih =>
      cases heval : evalCrepRuntimeExp state expression with
      | none => simp [evalCrepRuntimeExps, heval] at hleft
      | some value =>
          cases htail : evalCrepRuntimeExps state expressions with
          | none => simp [evalCrepRuntimeExps, heval, htail] at hleft
          | some values =>
              simp [evalCrepRuntimeExps, heval, htail] at hleft
              subst leftValues
              simp only [List.cons_append, evalCrepRuntimeExps, heval]
              rw [ih values htail]
              simp

private theorem evalPanSemStateExps_cons
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) (expressions : List (Exp (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64)) (values : List (PanValue (RiscV.Word 64))) :
    evalPanSemStateExps source (expression :: expressions) = some (value :: values) ↔
      evalPanSemStateExp source expression = some value ∧
      evalPanSemStateExps source expressions = some values := by
  unfold evalPanSemStateExps evalPanSemStateExp evalPanValueExps
  cases hhead : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
    cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
      source.globals source.memory source.baseAddress source.topAddress
      panSemBitVec64BytesInWord expressions
      (some (panSemBitVec64MemoryAccess source)) <;>
    simp [evalPanValueExp.evalPanValueExps, hhead, htail]

/-! HOL `eval_map_comp_exp_flat_eq` lifts the per-expression compiler value
relation over argument lists. This helper proves that list induction step
without claiming the per-expression theorem for unsupported constructors. -/
private theorem evalMapCompileArgsFlat_of_each
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hsource : evalPanSemStateExps source expressions = some values)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value)) :
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
      some (values.flatMap panValueFlatten) := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => simp [compileArgsHOL, evalCrepRuntimeExps]
      | cons value values =>
          simp [evalPanSemStateExps, evalPanValueExps,
            evalPanValueExp.evalPanValueExps] at hsource
  | cons expression expressions ih =>
      cases values with
      | nil =>
          have hsourceImpossible :
              evalPanSemStateExps source (expression :: expressions) ≠ some [] := by
            intro h
            cases hhead : evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
                expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
              cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
                source.globals source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord expressions
                (some (panSemBitVec64MemoryAccess source)) <;>
              simp [evalPanSemStateExps, evalPanValueExps,
                evalPanValueExp.evalPanValueExps, hhead, htail] at h
          exact False.elim (hsourceImpossible hsource)
      | cons value values =>
          obtain ⟨hhead, htail⟩ :=
            (evalPanSemStateExps_cons source expression expressions value values).mp hsource
          have hcompiledHead := heach expression (by simp) value hhead
          have heachTail : ∀ head, head ∈ expressions → ∀ item,
              evalPanSemStateExp source head = some item →
              evalCrepRuntimeExps target (compileExpHOL compilerContext head).1 =
                some (panValueFlatten item) := by
            intro head hmem item heval
            exact heach head (by simp [hmem]) item heval
          have hcompiledTail := ih values htail heachTail
          have happend := evalCrepRuntimeExps_append target
            (compileExpHOL compilerContext expression).1
            (compileArgsHOL compilerContext expressions)
            (panValueFlatten value) (values.flatMap panValueFlatten)
            hcompiledHead hcompiledTail
          simpa [compileArgsHOL, List.flatMap_cons] using happend

private theorem mapM_panTheWord_of_wordLab
    (locals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (slots : List Nat) (words : List (RiscV.Word 64))
    (hslots : slots.mapM (FLOOKUP locals) =
      some (words.map PanWordLab.word)) :
    slots.mapM (fun slot => (FLOOKUP locals slot).map panTheWord) = some words := by
  induction slots generalizing words with
  | nil =>
      cases words with
      | nil => simp
      | cons word words => simp at hslots
  | cons slot slots ih =>
      cases words with
      | nil =>
          simp only [List.mapM_cons] at hslots
          cases hlookup : FLOOKUP locals slot with
          | none => simp [hlookup] at hslots
          | some cell =>
              cases htail : slots.mapM (FLOOKUP locals) <;>
                simp [hlookup, htail] at hslots
      | cons word words =>
          simp only [List.mapM_cons] at hslots
          cases hlookup : FLOOKUP locals slot with
          | none => simp [hlookup] at hslots
          | some cell =>
              cases cell with
                | word cellWord =>
                  cases htail : slots.mapM (FLOOKUP locals) with
                  | none => simp [hlookup, htail] at hslots
                  | some cells =>
                      simp [hlookup, htail] at hslots
                      rcases hslots with ⟨hword, htailWords⟩
                      subst word
                      have htailLookup : slots.mapM (FLOOKUP locals) =
                          some (words.map PanWordLab.word) := by
                        rw [htail, htailWords]
                      have htailEval := ih words htailLookup
                      simp [List.mapM_cons, hlookup, panTheWord, htailEval]

/-! Flapjack-specific local-variable support toward HOL `compile_exp_val_rel`. `locals_rel`
provides the flattened target words for the source value, and target `.var`
evaluation reads those same slots through the production Crep locals map.
This handles one RV64 constructor, but does not state HOL's full case or
claim the general expression theorem `eval_map_comp_exp_flat_eq`. -/
theorem compileExpHOL_local_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (hlocals : localsRel context source.locals target.locals)
    (hsourceEval : evalPanSemStateExp source (.var .local name) = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.var .local name)).1 = some (panValueFlatten value) := by
  have hsource : FLOOKUP source.locals name = some value := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceEval
  obtain ⟨slots, hcontext, _, htargetWords, _⟩ :=
    localsRelLookupCtxt context source.locals target.locals name value hlocals hsource
  have htargetValues : slots.mapM
      (fun slot => (FLOOKUP target.locals slot).map panTheWord) =
      some (panValueFlatten value) := by
    exact mapM_panTheWord_of_wordLab target.locals slots (panValueFlatten value)
      htargetWords
  simp only [compileExpHOL, hcontext]
  rw [evalCrepRuntimeExps_vars_eq]
  exact htargetValues

/-! Flapjack-specific RV64 constant support toward HOL `compile_exp_val_rel`;
    the general expression theorem remains open. -/
theorem compileExpHOL_const_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (value : RiscV.Word 64) (sourceValue : PanValue (RiscV.Word 64))
    (hsourceEval : evalPanSemStateExp source (.const value) = some sourceValue) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).1 = some (panValueFlatten sourceValue) := by
  have hsourceValue : sourceValue = .word value := by
    have hword : PanValue.word value = sourceValue := by
      simpa [evalPanSemStateExp, evalPanValueExp] using hsourceEval
    exact hword.symm
  subst sourceValue
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp, panValueFlatten]

inductive compileArgConstOrLocal : Exp (RiscV.Word 64) → Prop where
  | const (value : RiscV.Word 64) : compileArgConstOrLocal (.const value)
  | localVar (name : String) : compileArgConstOrLocal (.var .local name)

/-! Call-argument list case when every argument is a constant or local
variable. This composes the exact Const/Local `compile_exp_val_rel` cases
through HOL `compile_args`; compound expressions remain to be ported. -/
theorem compileArgsHOL_constOrLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    cases hsupported expression hmem with
    | const word =>
        exact compileExpHOL_const_eval_flatten context source target word value heval
    | localVar name =>
        exact compileExpHOL_local_eval_flatten context source target name value
          hlocals heval
  simpa [compilerContext] using
    evalMapCompileArgsFlat_of_each compilerContext source target expressions values
      hsource heach

/-! One additional `compile_exp_val_rel` constructor: an `RStruct` whose
fields are each constants or local variables. Its nested argument list is
proved with the leaf cases above; this does not cover nested structs or other
compound expressions. -/
private theorem compileExpListHOL_flatMap_eq_compileArgsHOL
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (fields : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext fields).flatMap Prod.fst =
      compileArgsHOL compilerContext fields := by
  induction fields with
  | nil => simp [compileExpHOL.compileExpListHOL, compileArgsHOL]
  | cons field fields ih =>
      simp [compileExpHOL.compileExpListHOL, compileArgsHOL, ih]

theorem compileExpHOL_rStruct_constOrLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (fields : List (Exp (RiscV.Word 64)))
    (fieldValues : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ fields →
      compileArgConstOrLocal expression)
    (hsource : evalPanSemStateExp source (.rStruct fields) =
      some (.rStruct fieldValues)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rStruct fields)).1 =
      some (panValueFlatten (.rStruct fieldValues)) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
    simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
      evalPanValueExps] using hsource
  have hcompiled := compileArgsHOL_constOrLocal_eval_flatten context source target
    fields fieldValues hlocals hsupported hsourceFields
  simpa [compilerContext, compileExpHOL,
    compileExpListHOL_flatMap_eq_compileArgsHOL,
    panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled

inductive compileArgConstLocalOrStruct : Exp (RiscV.Word 64) → Prop where
  | const (value : RiscV.Word 64) : compileArgConstLocalOrStruct (.const value)
  | localVar (name : String) : compileArgConstLocalOrStruct (.var .local name)
  | rStruct (fields : List (Exp (RiscV.Word 64)))
      (hsupported : ∀ expression, expression ∈ fields →
        compileArgConstOrLocal expression) :
      compileArgConstLocalOrStruct (.rStruct fields)

/-! The Call argument list theorem with top-level `RStruct` arguments whose
fields are constants or locals. It remains a restricted subset of HOL's
`eval_map_comp_exp_flat_eq`; nested structures and other constructors remain
open. -/
theorem compileArgsHOL_constLocalOrStruct_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalOrStruct expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    cases hsupported expression hmem with
    | const word =>
        exact compileExpHOL_const_eval_flatten context source target word value heval
    | localVar name =>
        exact compileExpHOL_local_eval_flatten context source target name value
          hlocals heval
    | rStruct fields hfields =>
        cases value with
        | word word =>
            simp [evalPanSemStateExp, evalPanValueExp] at heval
        | rStruct fieldValues =>
            exact compileExpHOL_rStruct_constOrLocal_eval_flatten context source
              target fields fieldValues hlocals hfields heval
        | nStruct name fields =>
            simp [evalPanSemStateExp, evalPanValueExp] at heval
  simpa [compilerContext] using
    evalMapCompileArgsFlat_of_each compilerContext source target expressions values
      hsource heach

inductive compileArgConstLocalStructAddress : Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalOrStruct expression) :
      compileArgConstLocalStructAddress expression
  | baseAddress : compileArgConstLocalStructAddress .baseAddr
  | topAddress : compileArgConstLocalStructAddress .topAddr
  | bytesInWord : compileArgConstLocalStructAddress .bytesInWord

/-! Call argument results for all already-proved Const/Local/RStruct cases,
plus the three address/word-size constructors of HOL compile_exp_val_rel.
The state relation supplies the source/target address equalities. -/
theorem compileArgsHOL_constLocalStructAddress_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddress expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hbase, htop⟩
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    cases hsupported expression hmem with
    | baseAddress =>
        have hvalue : value = .word source.baseAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
          panValueFlatten, hbase]
    | topAddress =>
        have hvalue : value = .word source.topAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
          panValueFlatten, htop]
    | bytesInWord =>
        have hvalue : value = .word panSemBitVec64BytesInWord := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
          panValueFlatten, panSemBitVec64BytesInWord,
          CrepBytesInWord.bytesInWord]
    | existing _ supported =>
        cases supported with
        | const word =>
            exact compileExpHOL_const_eval_flatten context source target word value heval
        | localVar name =>
            exact compileExpHOL_local_eval_flatten context source target name value
              hlocals heval
        | rStruct fields hfields =>
            cases value with
            | word word =>
                simp [evalPanSemStateExp, evalPanValueExp] at heval
            | rStruct fieldValues =>
                exact compileExpHOL_rStruct_constOrLocal_eval_flatten context source
                  target fields fieldValues hlocals hfields heval
            | nStruct name fields =>
                simp [evalPanSemStateExp, evalPanValueExp] at heval
  simpa [compilerContext] using
    evalMapCompileArgsFlat_of_each compilerContext source target expressions values
      hsource heach

/-! Derive the production Crep callee lookup and parameter locals from the
state-owned source/target code maps. The argument words are arbitrary; their
length must match the flattened source parameter shapes. The HOL compiled
argument evaluation bridge that supplies those words remains a separate
obligation in the general Call case. -/
private theorem eraseDups_eq_self_of_nodup (values : List Nat)
    (hnodup : values.Nodup) : values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rw [List.eraseDups_cons]
      have hfilter : tail.filter (fun value => !(value == head)) = tail := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        have hne : value ≠ head := by
          intro heq
          subst value
          exact hhead hvalue
        simp [hne]
      rw [hfilter, ih htail]

theorem lookupCrepRuntimeCode_ofCodeRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (argumentWords : List (RiscV.Word 64))
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) = argumentWords.length) :
    ∃ targetLocals : Nat → Option (PanWordLab (RiscV.Word 64)),
      lookupCrepRuntimeCode function argumentWords target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
            (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) ∧
      targetLocals = ((List.range
        (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip argumentWords).foldl
          (fun locals (name, value) =>
            updateCrepRuntimeLocal locals name (.word value))
            (fun _ => none : Nat → Option (PanWordLab (RiscV.Word 64))) := by
  let names := List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup source.code) function =
      some (parameters, sourceBody, returnShape) := by
    change panSemCodeLookup source.code function = _
    exact hentry
  rcases codeRelImp context (panSemCodeAsLookup source.code) target.code hcode
      function parameters sourceBody returnShape hsourceLookup with
    ⟨_, _, htargetEntry⟩
  have hnamesLength : names.length = argumentWords.length := by
    simpa [names] using hargumentLength
  have hnamesEraseDups : names.eraseDups = names :=
    eraseDups_eq_self_of_nodup names (by simp [names, List.nodup_range])
  refine ⟨(names.zip argumentWords).foldl
      (fun locals (name, value) =>
        updateCrepRuntimeLocal locals name (.word value))
      (fun _ => none : Nat → Option (PanWordLab (RiscV.Word 64))), ?_, rfl⟩
  unfold lookupCrepRuntimeCode
  rw [htargetEntry]
  simp [names, hnamesLength, hnamesEraseDups, assignCrepRuntimeLocals]

/-! Compose the restricted HOL compiled-argument cases with the state-owned
code_rel lookup. For Const/Local/RStruct/address arguments, target argument
evaluation is derived from the source state evaluator, and the production
target callee lookup then uses those exact words. The explicit flattened
parameter-length premise is still an obligation for a full Call case. -/
theorem lookupCrepRuntimeCode_ofCodeRel_compiledArgs
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddress expression)
    (hsource : evalPanSemStateExps source expressions = some values)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (values.flatMap panValueFlatten).length) :
    ∃ targetLocals : Nat → Option (PanWordLab (RiscV.Word 64)),
      evalCrepRuntimeExps target
        (compileArgsHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expressions) = some (values.flatMap panValueFlatten) ∧
      lookupCrepRuntimeCode function (values.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have harguments := compileArgsHOL_constLocalStructAddress_eval_flatten
    context source target expressions values hstate hlocals hsupported hsource
  obtain ⟨targetLocals, hlookup, _⟩ :=
    lookupCrepRuntimeCode_ofCodeRel context source target function parameters
      sourceBody returnShape (values.flatMap panValueFlatten) hcode hentry
      hargumentLength
  exact ⟨targetLocals, by simpa [compilerContext] using harguments, hlookup⟩

/-! Compose the actual target exp_hdl/Return execution with the generic Crep
Call exception-dispatch induction step. The callee lookup and body execution
remain explicit inputs so the enclosing state/code relation proof can derive
them from the production target code map. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandler
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (destinations : List Nat) (exceptionCode : RiscV.Word 64)
    (function handlerVariable : String) (slot : Nat)
    (arguments : List (CrepExp (RiscV.Word 64))) (values : List (RiscV.Word 64))
    (body : CrepProg (RiscV.Word 64))
    (calleeLocals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (value : RiscV.Word 64)
    (harguments : evalCrepRuntimeExps caller arguments = some values)
    (hlookup : lookupCrepRuntimeCode function values caller.code =
      some (body, calleeLocals))
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (exceptionCode,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (.return [.var slot])))) = true)
    (hclock : caller.clock ≠ 0)
    (hcalleeBody : evalCrepRuntimeProg handler primitive 4
      (decCrepClock { caller with locals := calleeLocals }) body =
        some (.raised exceptionCode, calleeState))
    (hvariable : FLOOKUP context.vars handlerVariable = some (Shape.one, [slot]))
    (hslot : ∃ old, caller.locals slot = some old)
    (hglobal : calleeState.globals (0 : BitVec 5) = some (.word value)) :
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (exceptionCode,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (.return [.var slot])))) function arguments =
      some (.returned [value],
        clearCrepRuntimeLocals
          { crepRuntimeCallerState caller calleeState with
            locals := updateCrepRuntimeLocal caller.locals slot (.word value) }) := by
  have hhandlerBody : evalCrepRuntimeProg handler primitive 4
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (.seq (expHdlFiniteMap context.vars handlerVariable) (.return [.var slot])) =
        some (.returned [value],
          clearCrepRuntimeLocals
            { crepRuntimeCallerState caller calleeState with
              locals := updateCrepRuntimeLocal caller.locals slot (.word value) }) := by
    exact crepRuntimeExpHdlReturnOneWord handler primitive
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      context.vars handlerVariable slot value hvariable hslot hglobal
  exact evalCrepRuntimeCall_handlesRaisedBody handler primitive 4 caller
    destinations exceptionCode exceptionCode
    (.seq (expHdlFiniteMap context.vars handlerVariable) (.return [.var slot]))
    body function arguments values calleeLocals calleeState
    (.returned [value],
      clearCrepRuntimeLocals
        { crepRuntimeCallerState caller calleeState with
          locals := updateCrepRuntimeLocal caller.locals slot (.word value) })
    harguments hlookup hinfoValid hclock (by simp) hcalleeBody hhandlerBody

/-! Generalize target Call exception dispatch to an arbitrary compiled handler
body. The payload setup and handler-body evaluator hypotheses are explicit so
the enclosing induction can derive them from the one-word `exp_hdl` step and
the recursive body case. This proves target dispatch only; body-state
relations with the source evaluator remain separate obligations. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (destinations : List Nat) (caught exception : RiscV.Word 64)
    (function handlerVariable : String)
    (arguments : List (CrepExp (RiscV.Word 64))) (values : List (RiscV.Word 64))
    (body handlerBody : CrepProg (RiscV.Word 64))
    (calleeLocals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (payloadState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (fuel : Nat)
    (harguments : evalCrepRuntimeExps caller arguments = some values)
    (hlookup : lookupCrepRuntimeCode function values caller.code =
      some (body, calleeLocals))
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exception) = true)
    (hcalleeBody : evalCrepRuntimeProg handler primitive (fuel + 1)
      (decCrepClock { caller with locals := calleeLocals }) body =
        some (.raised exception, calleeState))
    (hpayload : evalCrepRuntimeProg handler primitive fuel
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, payloadState))
    (hhandlerBody : evalCrepRuntimeProg handler primitive fuel
      (fixCrepRuntimeClock (ε := FfiFinalEvent)
        { crepRuntimeCallerState caller calleeState with locals := caller.locals }
        (.normal, payloadState)).2 handlerBody =
        some handlerResult) :
    evalCrepRuntimeCall handler primitive (fuel + 2) caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody)))
      function arguments = some handlerResult := by
  have hhandlerRun : evalCrepRuntimeProg handler primitive (fuel + 1)
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody) =
        some handlerResult := by
    have hhandlerBody' : evalCrepRuntimeProg handler primitive fuel
        { payloadState with
          clock := min (crepRuntimeCallerState caller calleeState).clock
            payloadState.clock } handlerBody = some handlerResult := by
      simpa [fixCrepRuntimeClock] using hhandlerBody
    simp only [evalCrepRuntimeProg]
    rw [hpayload]
    simp only [fixCrepRuntimeClock]
    rw [hhandlerBody']
  have hresult := evalCrepRuntimeCall_handlesRaisedBody handler primitive
    (fuel + 1) caller destinations caught exception
    (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody)
    body function arguments values calleeLocals calleeState handlerResult
    harguments hlookup hinfoValid hclock hmatch hcalleeBody hhandlerRun
  exact hresult

/-! Target-side Call_Ret_Exception composition with the actual source and
target code maps. The source argument evaluator and code_rel derive the
production Crep argument result and callee lookup; the target callee-body
induction hypothesis then feeds the existing exp_hdl/Return execution proof.
This composes the target Call side only; the source Call result and resulting
state relations remain obligations of the enclosing HOL case. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandler_ofCodeRelArgs
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (slot : Nat)
    (destinations : List Nat) (exceptionCode value : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source caller)
    (hcode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hlocals : localsRel context source.locals caller.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddress expression)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (exceptionCode,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (.return [.var slot])))) = true)
    (hclock : caller.clock ≠ 0)
    (hcalleeIH : ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      evalCrepRuntimeProg handler primitive 4
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hvariable : FLOOKUP context.vars handlerVariable = some (Shape.one, [slot]))
    (hslot : ∃ old, caller.locals slot = some old)
    (hglobal : calleeState.globals (0 : BitVec 5) = some (.word value)) :
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (exceptionCode,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (.return [.var slot])))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) =
      some (.returned [value],
        clearCrepRuntimeLocals
          { crepRuntimeCallerState caller calleeState with
            locals := updateCrepRuntimeLocal caller.locals slot (.word value) }) := by
  obtain ⟨targetLocals, harguments, hlookup⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgs context source caller function
      parameters sourceBody returnShape expressions arguments hstate hcode hlocals
      hsupported hsourceArgs hentry hargumentLength
  exact evalCrepRuntimeCall_catchesRaisedOneWordHandler context handler primitive
    caller destinations exceptionCode function handlerVariable slot
    (compileArgsHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax } expressions)
    (arguments.flatMap panValueFlatten)
    (compileCodeRelProg
      (ctxtFc context.funcs context.eids
        (parameters.map Prod.fst) (parameters.map Prod.snd)
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
      sourceBody)
    targetLocals calleeState value harguments hlookup hinfoValid hclock
    (hcalleeIH targetLocals hlookup) hvariable hslot hglobal

/-! Connect the arbitrary-handler target Call dispatcher to the actual source
and target code maps. Source argument evaluation plus `stateRel`, `codeRel`,
and `localsRel` derive production target argument words and the state-owned
callee lookup; the recursive target callee and handler-body results remain
explicit IH inputs. Source Call results and post-state relations remain open. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofCodeRelArgs
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String)
    (destinations : List Nat) (caught exceptionCode : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (handlerBody : CrepProg (RiscV.Word 64))
    (calleeState payloadState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (fuel : Nat)
    (hstate : stateRel source caller)
    (hcode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hlocals : localsRel context source.locals caller.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddress expression)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    (hcalleeIH : ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      evalCrepRuntimeProg handler primitive (fuel + 1)
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hpayload : evalCrepRuntimeProg handler primitive fuel
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, payloadState))
    (hhandlerBody : evalCrepRuntimeProg handler primitive fuel
      (fixCrepRuntimeClock (ε := FfiFinalEvent)
        { crepRuntimeCallerState caller calleeState with locals := caller.locals }
        (.normal, payloadState)).2 handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive (fuel + 2) caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  obtain ⟨targetLocals, harguments, hlookup⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgs context source caller function
      parameters sourceBody returnShape expressions arguments hstate hcode hlocals
      hsupported hsourceArgs hentry hargumentLength
  exact evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody context handler
    primitive caller destinations caught exceptionCode function handlerVariable
    (compileArgsHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expressions)
    (arguments.flatMap panValueFlatten)
    (compileCodeRelProg
      (ctxtFc context.funcs context.eids
        (parameters.map Prod.fst) (parameters.map Prod.snd)
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
      sourceBody)
    handlerBody targetLocals calleeState payloadState handlerResult fuel
    harguments hlookup hinfoValid hclock hmatch (hcalleeIH targetLocals hlookup)
    hpayload hhandlerBody

/-! Feed relation-aware handler-body induction hypotheses through the actual
state-owned target Call. The one-word `exp_hdl` relation helper derives the
target payload state and all four relations from the source and target callee
post-states; the handler-body IH then supplies its target execution. This is
still target evaluation composition: the source Call result and its final
post-state relation are separate obligations. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofCodeRelArgs_relations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (slot : Nat)
    (old : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode value : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (handlerBody : CrepProg (RiscV.Word 64))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (hinitialState : stateRel source caller)
    (hcallCode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hcalleeState : stateRel sourceAfterCallee calleeState)
    (hcalleeCode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      calleeState.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hsource : FLOOKUP source.locals handlerVariable = some old)
    (hvariable : FLOOKUP context.vars handlerVariable =
      some (Shape.one, [slot]))
    (hslot : ∃ current, caller.locals slot = some current)
    (hglobal : calleeState.globals (0 : BitVec 5) = some (.word value))
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddress expression)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    (hcalleeIH : ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      evalCrepRuntimeProg handler primitive 4
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hhandlerIH : ∀ targetPost,
      evalCrepRuntimeProg handler primitive 3
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, targetPost) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable (.word value) }
        targetPost →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable (.word value)) targetPost.locals →
      evalCrepRuntimeProg handler primitive 3
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  obtain ⟨targetPost, hpayload, hstatePost, hcodePost, hexcpPost, hlocalsPost⟩ :=
    crepRuntimeExpHdlOneWord_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable slot
      old value hcalleeState hcalleeCode hexcp hlocals hsource hvariable hslot hglobal
  have hhandlerBody := hhandlerIH targetPost hpayload hstatePost hcodePost
    hexcpPost hlocalsPost
  exact evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofCodeRelArgs
    context handler primitive source caller function handlerVariable destinations
    caught exceptionCode parameters sourceBody returnShape expressions arguments
    handlerBody calleeState targetPost handlerResult 3 hinitialState
    hcallCode
    hlocals hsupported hsourceArgs hentry hargumentLength hinfoValid hclock hmatch
    hcalleeIH (by simpa [crepRuntimeCallerState] using hpayload) hhandlerBody

/-! Fixed-RV64 actual-state Call simulation for a matching one-word exception
handler. The source call and target callee both resolve through their
state-owned code maps; the target handler reads the raised payload through
`exp_hdl`/`globals_lookup` and returns its flattened word. This is untagged
induction support for HOL `pc_compile_correct[Call_Ret_Exception]`. -/
theorem panToCrepPcCompileCorrectCallCatchRaiseOneWordCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function exception handlerVariable : String) (slot : Nat)
    (exceptionCode value oldValue : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals)
    (hcontextException : FLOOKUP context.eids exception = some exceptionCode)
    (hentry : panSemCodeLookup sourceState.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : sourceState.exceptionShapes exception = some .one)
    (hvariable : FLOOKUP context.vars handlerVariable = some (Shape.one, [slot]))
    (hsourceLocal : FLOOKUP sourceState.locals handlerVariable =
      some (.word oldValue))
    (hclock : targetState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) :=
      .call (some (none, some (exception, handlerVariable,
        .return (.var .local handlerVariable)))) function []
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi [.word value]), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 7 targetState
        (compileCodeRelProg context program) = some (.returned [value], targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      globalsLookup targetPost (.word value) = some [.word value] ∧
      decPanClock sourceState.clock = targetPost.clock := by
  let program : Prog (RiscV.Word 64) :=
    .call (some (none, some (exception, handlerVariable,
      .return (.var .local handlerVariable)))) function []
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.returned (fun _ => none) sourceState.globals sourceState.memory
      sourceState.ffi [.word value]), decPanClock sourceState.clock)
  change panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState (.call (some (none, some (exception, handlerVariable,
        .return (.var .local handlerVariable)))) function []) = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 7 targetState
        (compileCodeRelProg context
          (.call (some (none, some (exception, handlerVariable,
            .return (.var .local handlerVariable)))) function [])) =
          some (.returned [value], targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      globalsLookup targetPost (.word value) = some [.word value] ∧
      decPanClock sourceState.clock = targetPost.clock
  have hsourceClock : sourceState.clock ≠ 0 := by
    rcases hstate with ⟨_, _, _, _, _, hclockRel, _, _, _, _⟩
    omega
  have hsourceLocal : sourceState.locals handlerVariable =
      some (.word oldValue) := hsourceLocal
  have hsource := panSemEvaluateRiscV64CodeState_callCatchRaiseOneWord_ofEntry
    sourceContext sourcePrimitive sourceHandler sourceState function exception
    handlerVariable oldValue value hentry hexception hsourceLocal hsourceClock
  have hsourceRun : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using hsource
  obtain ⟨sourceSlots, hsourceContext, _, _, _⟩ :=
    localsRelLookupCtxt context sourceState.locals targetState.locals
      handlerVariable (.word oldValue) hlocals hsourceLocal
  have hslotPair : (panValueShape [] (.word oldValue), sourceSlots) =
      (Shape.one, [slot]) := by
    exact Option.some.inj (hsourceContext.symm.trans hvariable)
  have hsourceSlots : sourceSlots = [slot] := congrArg Prod.snd hslotPair
  obtain ⟨targetSlots, htargetContext, _, htargetWords, _⟩ :=
    localsRelLookupCtxt context sourceState.locals targetState.locals
      handlerVariable (.word oldValue) hlocals hsourceLocal
  have htargetSlots : targetSlots = [slot] := by
    have hpair : (panValueShape [] (.word oldValue), targetSlots) =
        (Shape.one, [slot]) := by
      exact Option.some.inj (htargetContext.symm.trans hvariable)
    exact congrArg Prod.snd hpair
  have htargetMap : List.mapM (FLOOKUP targetState.locals) [slot] =
      some ((panValueFlatten (.word oldValue)).map PanWordLab.word) := by
    simpa [htargetSlots] using htargetWords
  have htargetMapWord : (FLOOKUP targetState.locals slot).bind (fun cell => some [cell]) =
      some [PanWordLab.word oldValue] := by
    simpa [List.mapM_cons, panValueFlatten] using htargetMap
  have htargetSlot : targetState.locals slot = some (.word oldValue) := by
    cases hlookup : FLOOKUP targetState.locals slot with
    | none => simp [hlookup] at htargetMapWord
    | some cell =>
        cases cell with
        | word word =>
            have hword : word = oldValue := by
              simpa [hlookup] using htargetMapWord
            subst word
            simpa [FLOOKUP] using hlookup

  have hsourceCode : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([], .raise exception (.const value), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context (panSemCodeAsLookup sourceState.code)
    targetState.code hcode function [] (.raise exception (.const value)) .one hsourceCode
  rcases hcodeEntry with ⟨_, hfunction, _⟩
  let functionContext := ctxtFc context.funcs context.eids [] [] []
  let targetBody : CrepProg (RiscV.Word 64) :=
    .seq (.dec 1 (.const value)
      (.seq (.storeGlob (0 : BitVec 5) (.var 1)) .skip))
      (.raise exceptionCode)
  have hcompiledBody : compileCodeRelProg functionContext
      (.raise exception (.const value)) = targetBody := by
    simp [functionContext, targetBody, compileCodeRelProg, compileProgHOL,
      compileExpHOL, freshNamesHOL, ctxtFc, maxList, hcontextException,
      nestedDecs, crepNestedSeq, storeGlobals]
  have hemptySlots :
      List.range (Shape.shapeSize (.comb ([] : List Shape))) = [] := by
    simp [Shape.shapeSize]
  obtain ⟨targetCalleeLocals, htargetLookup, htargetCalleeLocalsEq⟩ :=
    lookupCrepRuntimeCode_ofCodeRel context sourceState targetState function []
      (.raise exception (.const value)) .one [] hcode hentry (by simp [Shape.shapeSize])
  have htargetLookup' : lookupCrepRuntimeCode function [] targetState.code =
      some (targetBody, fun _ => none) := by
    have hlocals : targetCalleeLocals = (fun _ => none) := by
      simpa [hemptySlots, Shape.shapeSize] using htargetCalleeLocalsEq
    simpa [hemptySlots, Shape.shapeSize, functionContext, hcompiledBody, hlocals]
      using htargetLookup

  let returnSlot := context.vmax + 1
  have hfunctionLookup : context.funcs function = some ([], Shape.one) := by
    simpa [FLOOKUP] using hfunction
  have hexceptionLookup : context.eids exception = some exceptionCode := by
    simpa [FLOOKUP] using hcontextException
  have hvariableLookup : context.vars handlerVariable = some (Shape.one, [slot]) := by
    simpa [FLOOKUP] using hvariable
  let continuation : CrepProg (RiscV.Word 64) :=
    .seq (expHdlFiniteMap context.vars handlerVariable)
      (.return [.var slot])
  have hcompiledCall : compileCodeRelProg context program =
      .dec returnSlot (.const 0)
        (.call (some ([returnSlot], some (exceptionCode, continuation))) function []) := by
    simp [program, returnSlot, continuation, compileCodeRelProg, compileProgHOL,
      compileArgsHOL, compileExpHOL, functionReturnNamesHOL, allocatedNamesHOL,
      hfunctionLookup,
      hexceptionLookup, expHdlFiniteMap, hvariableLookup, loadGlobals, panMap2,
      crepNestedSeq, nestedDecs, FLOOKUP]

  let targetCaller : CrepRuntimeState (RiscV.Word 64) σ :=
    { targetState with locals :=
      (updateCrepRuntimeLocal targetState.locals returnSlot (.word 0)) }
  let calleeState : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetState with
      locals := fun _ => none
      globals := updateCrepRuntimeGlobal targetState.globals
        (0 : BitVec 5) (.word value) }
  have hcalleeBody : evalCrepRuntimeProg targetHandler targetPrimitive 4
      (decCrepClock { targetCaller with locals := fun _ => none }) targetBody =
        some (.raised exceptionCode, calleeState) := by
    simp [targetBody, calleeState, targetCaller, evalCrepRuntimeProg,
      evalCrepRuntimeExp, decCrepClock, updateCrepRuntimeLocal,
      restoreCrepRuntimeStep, fixCrepRuntimeClock, setCrepRuntimeGlobals,
      clearCrepRuntimeLocals, panTheWord]
  have hcallerSlot : ∃ old, targetCaller.locals slot = some old := by
    by_cases heq : (returnSlot == slot)
    · exact ⟨.word 0, by simp [targetCaller, updateCrepRuntimeLocal, heq]⟩
    · exact ⟨.word oldValue,
        by simp [targetCaller, updateCrepRuntimeLocal, heq, htargetSlot]⟩
  have hcallNames : ([returnSlot].eraseDups).length = 1 := by
    simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  have hcallInfo : crepRuntimeCallInfoValid
      (some ([returnSlot], some (exceptionCode, continuation)) :
        Option (List Nat × Option ((RiscV.Word 64) × CrepProg (RiscV.Word 64)))) = true := by
    simp [crepRuntimeCallInfoValid, hcallNames]
  have htargetCall := evalCrepRuntimeCall_catchesRaisedOneWordHandler context
    targetHandler targetPrimitive targetCaller [returnSlot] exceptionCode
    function handlerVariable slot [] [] targetBody (fun _ => none) calleeState
    value (by simp [evalCrepRuntimeExps]) htargetLookup' hcallInfo
    (by simpa [targetCaller] using hclock) hcalleeBody hvariable hcallerSlot
    (by simp [calleeState, updateCrepRuntimeGlobal])
  have htargetCall' : evalCrepRuntimeCall targetHandler targetPrimitive 5
      targetCaller (some ([returnSlot], some (exceptionCode, continuation))) function [] =
      some (.returned [value],
        clearCrepRuntimeLocals
          { crepRuntimeCallerState targetCaller calleeState with
            locals := updateCrepRuntimeLocal targetCaller.locals slot (.word value) }) := by
    simpa [continuation] using htargetCall
  let targetPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetState with
      locals := (fun candidate =>
        if returnSlot == candidate then targetState.locals candidate else none)
      globals := updateCrepRuntimeGlobal targetState.globals
        (0 : BitVec 5) (.word value) }
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 7
      targetState (compileCodeRelProg context program) =
        some (.returned [value], targetPost) := by
    rw [hcompiledCall]
    simp only [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp]
    rw [htargetCall']
    simp [targetPost, targetCaller, calleeState, decCrepClock,
      crepRuntimeCallerState, restoreCrepRuntimeStep, clearCrepRuntimeLocals,
      beq_iff_eq]
    funext candidate
    by_cases hcandidate : returnSlot = candidate <;> simp [hcandidate]
  refine ⟨hsourceRun, targetPost, htargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
      hclockRel, hbe, hffi, hbase, htop⟩
    simp [stateRel, panSemCodeStateAfter, sourceResult, targetPost,
      decCrepClock, decPanClock, hmem, hmemaddrs, hshared, hstructs,
      hglobals, hclockRel, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp
  · simp [globalsLookup, targetPost, panSemShapeOf, updateCrepRuntimeGlobal]
  · rcases hstate with ⟨_, _, _, _, _, hclockRel, _, _, _, _⟩
    simp [targetPost, decCrepClock, decPanClock, hclockRel]

theorem panToCrepPcCompileCorrectCallRaiseOneWordExceptionCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function exception : String) (exceptionCode : RiscV.Word 64)
    (value : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (_hlocals : localsRel context sourceState.locals targetState.locals)
    (hcontextException : FLOOKUP context.eids exception = some exceptionCode)
    (hentry : panSemCodeLookup sourceState.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : sourceState.exceptionShapes exception = some .one)
    (hclock : sourceState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) := .call none function []
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.raised (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi exception (.word value)), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 8 targetState
        (compileCodeRelProg context program) =
          some (.raised exceptionCode, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      globalsLookup targetPost (.word value) = some [.word value] ∧
      decPanClock sourceState.clock = targetPost.clock := by
  let program : Prog (RiscV.Word 64) := .call none function []
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.raised (fun _ => none) sourceState.globals sourceState.memory
      sourceState.ffi exception (.word value)), decPanClock sourceState.clock)
  let functionContext := ctxtFc context.funcs context.eids [] [] []
  let targetBody : CrepProg (RiscV.Word 64) :=
    .seq (.dec 1 (.const value)
      (.seq (.storeGlob (0 : BitVec 5) (.var 1)) .skip))
      (.raise exceptionCode)
  let targetPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetState with
      locals := fun _ => none
      globals := updateCrepRuntimeGlobal targetState.globals
        (0 : BitVec 5) (.word value) }
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
  have hsource : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using
      panSemEvaluateRiscV64CodeState_callRaiseOneWordException_ofEntry
        sourceContext sourcePrimitive sourceHandler sourceState function
        exception value hentry hexception hclock
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([], .raise exception (.const value), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context
    (panSemCodeAsLookup sourceState.code) targetState.code hcode function
    [] (.raise exception (.const value)) .one hsourceLookup
  rcases hcodeEntry with ⟨_hlocalized, _hfunction, htargetLookup⟩
  have hcompiledBody : compileCodeRelProg functionContext
      (.raise exception (.const value)) = targetBody := by
    simp [functionContext, targetBody, compileCodeRelProg, compileProgHOL,
      compileExpHOL, freshNamesHOL, ctxtFc, maxList, hcontextException,
      nestedDecs, crepNestedSeq, storeGlobals]
  have htargetCode : FLOOKUP targetState.code function = some ([], targetBody) := by
    simpa [Shape.shapeSize, functionContext, maxList, hcompiledBody] using htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [] targetState.code =
      some (targetBody, fun _ => none) := by
    unfold lookupCrepRuntimeCode
    rw [htargetCode]
    simp [assignCrepRuntimeLocals]
  have htargetClock : targetState.clock ≠ 0 := by omega
  have hcompiledCall : compileCodeRelProg context program =
      .call none function [] := by
    simp [program, compileCodeRelProg, compileProgHOL, compileArgsHOL]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 8
      targetState (compileCodeRelProg context program) =
        some (.raised exceptionCode, targetPost) := by
    simp [hcompiledCall, targetPost, targetBody,
      evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeCall,
      evalCrepRuntimeExps, evalCrepRuntimeExp, htargetCallLookup,
      htargetClock, decCrepClock, fixCrepRuntimeClock,
      restoreCrepRuntimeStep, updateCrepRuntimeLocal, clearCrepRuntimeLocals,
      crepRuntimeCallerState, crepRuntimeCallInfoValid,
      setCrepRuntimeGlobals, panTheWord]
  refine ⟨hsource, targetPost, htargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      decCrepClock, decPanClock, hmem, hmemaddrs, hshared, hstructs,
      hglobals, hclockRel, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp
  · simp [globalsLookup, targetPost, panSemShapeOf,
      updateCrepRuntimeGlobal]
  · simp [targetPost, decPanClock, decCrepClock, hclockRel]
end Flapjack
