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
