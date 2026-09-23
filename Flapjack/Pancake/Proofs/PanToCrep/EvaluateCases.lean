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
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .skip =
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState .skip =
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
  refine ⟨panSemEvaluateCodeState_skip sourceContext sourcePrimitive sourceHandler
    targetState.bytesInWord sourceState, ?_⟩
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
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .break =
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState .break =
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
  refine ⟨panSemEvaluateCodeState_break sourceContext sourcePrimitive sourceHandler
    targetState.bytesInWord sourceState, ?_⟩
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
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .continue =
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState .continue =
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
  refine ⟨panSemEvaluateCodeState_continue sourceContext sourcePrimitive sourceHandler
    targetState.bytesInWord sourceState, ?_⟩
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
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .tick =
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState .tick =
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
  refine ⟨panSemEvaluateCodeState_tick sourceContext sourcePrimitive sourceHandler
    targetState.bytesInWord sourceState, ?_⟩
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
    (tag text : String) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.annot tag text) =
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState (.annot tag text) =
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
  refine ⟨panSemEvaluateCodeState_annot sourceContext sourcePrimitive sourceHandler
    targetState.bytesInWord sourceState tag text, ?_⟩
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
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function : FunName)
    (hentry : panSemCodeLookup state.code function = some ([], .skip, .one))
    (hclock : state.clock = 0) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.call none function [] : Prog α) =
      some (panValueFfiClockTimeout state.globals state.memory state.ffi state.clock) := by
  have hlookupCall : lookupPanSemCodeCall state.structs state.code function [] =
      some (.skip, .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  have hargs : evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord [] = some [] := by
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

/-! The zero-clock Call timeout branch at the production source/target state
boundary. This is a single induction branch, not the general HOL theorem. -/
theorem panToCrepPcCompileCorrectCallTimeoutCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α]
    (context : PanToCrepProofContext α)
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
    panSemEvaluateCodeState sourceContext sourcePrimitive sourceHandler
      targetState.bytesInWord sourceState (.call none function [] : Prog α) =
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
    sourceContext sourcePrimitive sourceHandler targetState.bytesInWord sourceState
    function hentry hclock
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
    simp [assignCrepValues]
  have htargetCallRun : evalCrepRuntimeCall targetHandler targetPrimitive
      (fuel + 1) targetState none function [] =
      some (.timeout, clearCrepRuntimeLocals targetState) := by
    simp [evalCrepRuntimeCall, evalCrepRuntimeExps, htargetCallLookup, htargetZero,
      crepRuntimeCallInfoValid, clearCrepRuntimeLocals]
  refine ⟨hsource, clearCrepRuntimeLocals targetState, ?_, ?_, ?_, ?_⟩
  · simpa [evalCrepRuntimeResult, evalCrepRuntimeProg, compileCodeRelProg,
      compileProgHOL, compileArgsHOL] using htargetCallRun
  · simp [stateRel, panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals, hclock, htargetZero, hmem, hmemaddrs,
      hshared, hstructs, hglobals, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals] using hcode
  · simpa [panSemCodeStateAfter, panValueFfiClockTimeout,
      clearCrepRuntimeLocals] using hexcp
end Flapjack
