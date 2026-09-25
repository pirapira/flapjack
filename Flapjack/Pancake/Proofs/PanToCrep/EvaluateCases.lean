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

/-- Width-indexed, fuel-bounded evaluator bridge for the HOL
    `pc_compile_correct[Skip]` proof branch (`pan_to_crepProofScript.sml:493`).
    It preserves the `state_rel`, width-indexed `code_rel`, `excp_rel`, and
    `locals_rel` clauses, with `codeRelW` at both code boundaries. It derives
    successful source and target runs from the incoming relations; the target
    run uses an existential fuel. This is useful case support, but it is not
    the full HOL Skip case: HOL's `panSem$evaluate` and `crepSem$evaluate` are
    total functions returning `(result, state)`, while these Lean interfaces
    return `Option` results from fuel-indexed evaluators. In particular, the
    Lean target `.normal` result is not itself HOL's `NONE` result. A faithful
    total-evaluator interface and its result/state correspondence are still
    prerequisites for restating the full HOL boundary. Keep this untagged. -/
theorem panToCrepPcCompileCorrectSkipFuelBoundedBridgeW
    (width : Nat)
    [BEq String]
    (context : PanToCrepProofContext (BitVec width))
    (sourceModel : PanMemoryModel (BitVec width)) (sourceBytesInWord : BitVec width)
    (sourceContext : PanValueFfiContext (BitVec width))
    (sourcePrimitive : PanPrimitiveHandler (BitVec width))
    (sourceHandler : PanValueStatefulFfiHandler (BitVec width) σ)
    (targetHandler : CrepRuntimeFfiHandler (BitVec width) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (BitVec width))
    (sourceState : PanSemState (BitVec width) (FfiState σ))
    (targetState : CrepRuntimeState (BitVec width) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRelW width context
      (panSemCodeAsLookup sourceState.code) targetState.code)
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
      codeRelW width context
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
  have hcodeGeneric :=
    (codeRelW_iff_codeRel width context
      (panSemCodeAsLookup sourceState.code) targetState.code).mp hcode
  rcases panToCrepPcCompileCorrectSkipCodeState context sourceModel sourceBytesInWord
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      sourceState targetState hstate hcodeGeneric hexcp hlocals with
    ⟨hsource, targetFuel, targetResult, targetPost, hrun, hstatePost,
      hcodePost, hexcpPost, hresult, hlocalsPost⟩
  refine ⟨hsource, targetFuel, targetResult, targetPost, hrun, hstatePost, ?_,
    hexcpPost, hresult, hlocalsPost⟩
  exact (codeRelW_iff_codeRel width context
    (panSemCodeAsLookup (panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock)).code)
    targetPost.code).mpr hcodePost

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
          simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
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
                  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
                    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
                    panValueReturnResult, evalPanValueExpCounted, evalPanValueExp,
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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCodeLookup,
      FUPDATE_LIST]
    funext key
    rfl
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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCodeLookup,
      FUPDATE_LIST]
    funext key
    rfl
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
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    panValueReturnResult, evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
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
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    panValueReturnResult, evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
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
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueExpCounted, evalPanValueExp,
    hargs, hcallee, hexception, hclock, panValueShape, panShapeMatches,
    decPanClock]

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
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    panValueReturnResult, evalPanValueExpCounted, evalPanValueExp,
    hargs, hcallee, hexception,
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
    (hhandlerAssignment : panValueAssignmentValid state.structs state.locals
      (fun _ => none) .local handlerVariable exceptionValue = true)
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
    calleeRaisedLocals hcalleeBody hexceptionShape hhandlerAssignment hhandlerBody

/-! Lift the source-side raised-handler IH composition to the production
RISC-V `PanSemState` evaluator. Both body premises use the source Call's
canonical state-code-derived budget minus the two dispatch steps; the
canonical-fuel lower bound proves the wrapper equation internally, so callers
do not supply an `hsourceFuel` premise. The code field remains state-owned and
is preserved in the projected post-state. Target simulation remains a separate
obligation. -/
theorem panSemEvaluateRiscV64CodeState_call_catchesRaisedBody_ofState
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
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
      state.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel state
        (.call (some (none, some (exception, handlerVariable, handlerProgram)))
          function arguments) - 2) calleeLocals state.globals
      state.memory state.ffi (decPanClock state.clock) body
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
      some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory
        calleeFfi exception exceptionValue), calleeClock))
    (hexceptionShape : ∃ shape,
      state.exceptionShapes exception = some shape ∧
      panShapeMatches (panValueShape state.structs exceptionValue) shape = true)
    (hhandlerAssignment : panValueAssignmentValid state.structs state.locals
      (fun _ => none) .local handlerVariable exceptionValue = true)
    (hhandlerBody : evalPanValueFfiClockCodeProg context primitive handler
      state.structs state.code state.exceptionShapes state.baseAddress
      state.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel state
        (.call (some (none, some (exception, handlerVariable, handlerProgram)))
          function arguments) - 2)
      (updatePanValueMap state.locals handlerVariable exceptionValue)
      calleeGlobals calleeMemory calleeFfi
      (min (decPanClock state.clock) calleeClock) handlerProgram
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
      some handlerResult) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.call (some (none, some (exception, handlerVariable, handlerProgram)))
        function arguments) = some handlerResult ∧
    (panSemCodeStateAfter state handlerResult).code = state.code := by
  let fuel := panSemCodeEvaluateFuel state
    (.call (some (none, some (exception, handlerVariable, handlerProgram)))
      function arguments) - 2
  have hfuel : panSemCodeEvaluateFuel state
      (.call (some (none, some (exception, handlerVariable, handlerProgram)))
        function arguments) = fuel + 2 := by
    dsimp [fuel]
    have htwo := panSemCodeEvaluateFuel_call_two_le state
      (some (none, some (exception, handlerVariable, handlerProgram)))
      function arguments
    omega
  have hcall := panSemEvaluateRiscV64CodeCall_catchesRaisedBody_ofState
    context primitive handler state fuel function exception handlerVariable
    arguments values returnShape body calleeLocals calleeRaisedLocals
    calleeGlobals calleeMemory calleeFfi exceptionValue calleeClock handlerProgram
    handlerResult harguments hcallee hclock hcalleeBody hexceptionShape
    hhandlerAssignment hhandlerBody
  refine ⟨?_, panSemCodeStateAfter_preserves_code state handlerResult⟩
  change panSemEvaluateCodeStateWithMemoryModel context primitive handler
    panSemBitVec64WordModel panSemBitVec64BytesInWord state
    (.call (some (none, some (exception, handlerVariable, handlerProgram)))
      function arguments) = some handlerResult
  unfold panSemEvaluateCodeStateWithMemoryModel panSemEvaluateCodeState
    panSemEvaluateCodeStateWithFuel
  rw [hfuel]
  simpa [evalPanValueFfiClockCodeProg, panSemBitVec64MemoryAccess] using hcall


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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCodeLookup,
      FUPDATE_LIST]
    funext key
    by_cases hkey : key = 0
    · subst key
      simp [FUPDATE]
    · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
      simp [FUPDATE, FEMPTY, hzero, hkey]
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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCodeLookup,
      FUPDATE_LIST]
    funext key
    by_cases hkey : key = 0
    · subst key
      simp [FUPDATE]
    · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
      simp [FUPDATE, FEMPTY, hzero, hkey]
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
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
    panValueReturnResult, evalPanValueExpCounted, evalPanValueExp, hargs, hcallee, hclock,
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

/-! State-owned DecCall/Tick source equation. The nonempty finite-support code
entry supplies the callee body; the evaluator then executes the non-Skip
continuation under the caller's updated local and performs both HOL clock
decrements. This is source-side proof infrastructure, not a complete
Pan-to-Crep theorem. -/
theorem panSemEvaluateCodeState_decCallTick_ofEntry
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (function name : FunName) (value : α)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : 2 ≤ state.clock)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state
      (.decCall name .one function [.const value] .tick : Prog α)
        (memoryAccess := memoryAccess) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        decPanClock (decPanClock state.clock)) := by
  let program : Prog α :=
    .decCall name .one function [.const value] .tick
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
          fun key => if key == "parameter" then some (.word value) else none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters, panValueShape,
      panShapeMatches]
    all_goals
      funext key
      simp [updatePanValueMap, beq_iff_eq]
  have hclockNonzero : state.clock ≠ 0 := by omega
  have hcontinuationClockNonzero : decPanClock state.clock ≠ 0 := by
    simp [decPanClock]
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  have hfuelConcrete : panSemCodeEvaluateFuel state
      (.decCall name .one function [.const value] .tick : Prog α) = tail + 5 := by
    simpa [program] using hfuel
  rw [hfuelConcrete]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall,
    panValueCallArgumentsValue, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps, panValueReturnResult, evalPanValueExpCounted,
    evalPanValueExp, hargs, hcallee, hclockNonzero,
    hcontinuationClockNonzero, panValueShape, panShapeMatches,
    panValueFfiClockRestoreLocal, panValueExpStepCost,
    restorePanValueFfiLocal, decPanClock]
  all_goals
    funext key
    by_cases hkey : key = name
    · simp [restorePanValueLocal, hkey]
    · simp [restorePanValueLocal, updatePanValueMap, beq_iff_eq, hkey]

theorem panSemEvaluateRiscV64CodeState_decCallTick_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function name : FunName) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : 2 ≤ state.clock) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.decCall name .one function [.const value] .tick : Prog (RiscV.Word 64)) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        decPanClock (decPanClock state.clock)) := by
  simpa [panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess] using
      panSemEvaluateCodeState_decCallTick_ofEntry context
        primitive handler panSemBitVec64BytesInWord state function name value hentry hclock
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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCodeLookup,
      FUPDATE_LIST]
    funext key
    by_cases hkey : key = 0
    · subst key
      simp [FUPDATE]
    · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
      simp [FUPDATE, FEMPTY, hzero, hkey]
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

/-! The DecCall compiler lowers its continuation after the target Call in a
`seq`.  This bridge is the recursive continuation step: the source continuation
must actually run, and its source-run-to-target-run IH supplies the target
continuation execution and all post-state relations.  The target Call prefix
is the result of the separate callee IH.  This is intentionally untagged: it
composes the two recursive hypotheses but does not claim the whole HOL
`pc_compile_correct` theorem. -/
theorem panToCrepDecCallTickContinuationSeqOfSourceRunIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (fuel : Nat)
    (sourceContinuationResult : PanValueFfiClockResult (RiscV.Word 64) σ)
    (sourceContinuationState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetCallStart targetCallPost :
      CrepRuntimeState (RiscV.Word 64) σ)
    (slots : List Nat) (function : FunName)
    (arguments : List (CrepExp (RiscV.Word 64)))
    (hsourceContinuation :
      panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
        sourceContinuationState .tick = some sourceContinuationResult)
    (hstate : stateRel sourceContinuationState
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2)
    (hcode : codeRel context
      (panSemCodeAsLookup sourceContinuationState.code)
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.code)
    (hexcp : excpRel context.eids sourceContinuationState.exceptionShapes)
    (hlocals : localsRel context sourceContinuationState.locals
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.locals)
    (hcallPrefix :
      evalCrepRuntimeResult targetHandler targetPrimitive fuel targetCallStart
        (.call (some (slots, none)) function arguments) =
          some (.normal, targetCallPost))
    (hcontinuationIH :
      stateRel sourceContinuationState
        (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
          (.normal, targetCallPost)).2 →
      codeRel context (panSemCodeAsLookup sourceContinuationState.code)
        (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
          (.normal, targetCallPost)).2.code →
      excpRel context.eids sourceContinuationState.exceptionShapes →
      localsRel context sourceContinuationState.locals
        (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
          (.normal, targetCallPost)).2.locals →
      panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
          sourceContinuationState .tick = some sourceContinuationResult →
        ∃ targetResult targetPost,
          evalCrepRuntimeResult targetHandler targetPrimitive fuel
            (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
              (.normal, targetCallPost)).2
            (compileCodeRelProg context .tick) =
              some (targetResult, targetPost) ∧
          stateRel (panSemCodeStateAfter sourceContinuationState
            sourceContinuationResult) targetPost ∧
          codeRel context (panSemCodeAsLookup
            (panSemCodeStateAfter sourceContinuationState
              sourceContinuationResult).code) targetPost.code ∧
          excpRel context.eids
            (panSemCodeStateAfter sourceContinuationState
              sourceContinuationResult).exceptionShapes ∧
          localsRel context
            (panSemCodeStateAfter sourceContinuationState
              sourceContinuationResult).locals targetPost.locals ∧
          (sourceContinuationState.clock = 0 → targetResult = .timeout) ∧
          (sourceContinuationState.clock ≠ 0 → targetResult = .normal)) :
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1) targetCallStart
        (.seq (.call (some (slots, none)) function arguments)
          (compileCodeRelProg context .tick)) =
            some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceContinuationState
        sourceContinuationResult) targetPost ∧
      codeRel context (panSemCodeAsLookup
        (panSemCodeStateAfter sourceContinuationState
          sourceContinuationResult).code) targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceContinuationState
          sourceContinuationResult).exceptionShapes ∧
      localsRel context
        (panSemCodeStateAfter sourceContinuationState
          sourceContinuationResult).locals targetPost.locals ∧
      (sourceContinuationState.clock = 0 → targetResult = .timeout) ∧
      (sourceContinuationState.clock ≠ 0 → targetResult = .normal) := by
  obtain ⟨targetResult, targetPost, hcontinuationRun, hpostState,
    hpostCode, hpostExcp, hpostLocals, hresultZero, hresultPositive⟩ :=
      hcontinuationIH hstate hcode hexcp hlocals hsourceContinuation
  refine ⟨targetResult, targetPost, ?_, hpostState, hpostCode, hpostExcp,
    hpostLocals, hresultZero, hresultPositive⟩
  change evalCrepRuntimeProg targetHandler targetPrimitive (fuel + 1)
    targetCallStart
    (.seq (.call (some (slots, none)) function arguments)
      (compileCodeRelProg context .tick)) = some (targetResult, targetPost)
  change evalCrepRuntimeProg targetHandler targetPrimitive fuel targetCallStart
    (.call (some (slots, none)) function arguments) =
      some (.normal, targetCallPost) at hcallPrefix
  change evalCrepRuntimeProg targetHandler targetPrimitive fuel
    (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
      (.normal, targetCallPost)).2
    (compileCodeRelProg context .tick) = some (targetResult, targetPost)
    at hcontinuationRun
  have hcont : evalCrepRuntimeProg targetHandler targetPrimitive fuel
      { targetCallPost with
        clock := min targetCallStart.clock targetCallPost.clock }
      (compileCodeRelProg context .tick) = some (targetResult, targetPost) := by
    simpa [fixCrepRuntimeClock] using hcontinuationRun
  simp [evalCrepRuntimeProg, hcallPrefix, fixCrepRuntimeClock, hcont]

/-! Produce the identity-callee prefix and continuation-entry relations from
the actual source/target code relation. This removes the free target-call-run
and post-call relation assumptions for the one-word `return parameter`
DecCall slice; the remaining continuation simulation is supplied by its
recursive Tick IH below. -/
theorem panToCrepDecCallReturnParameterPrefixFromCodeRel
    (context : PanToCrepProofContext (RiscV.Word 64))
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
    let targetSlot := context.vmax + 1
    let continuationContext : PanToCrepProofContext (RiscV.Word 64) :=
      { context with
        vars := FUPDATE context.vars (name, (.one, [targetSlot]))
        vmax := context.vmax + 1 }
    let sourceContinuation : PanSemState (RiscV.Word 64) (FfiState σ) :=
      { sourceState with
        locals := updatePanValueMap sourceState.locals name (.word value)
        clock := decPanClock sourceState.clock }
    let targetCallStart : CrepRuntimeState (RiscV.Word 64) σ :=
      { targetState with
        locals := updateCrepRuntimeLocal targetState.locals targetSlot (.word 0) }
    let targetCallPost : CrepRuntimeState (RiscV.Word 64) σ :=
      { decCrepClock targetCallStart with
        locals := updateCrepRuntimeLocal targetCallStart.locals targetSlot
          (.word value) }
    evalCrepRuntimeResult targetHandler targetPrimitive 3 targetCallStart
      (.call (some ([targetSlot], none)) function [.const value]) =
        some (.normal, targetCallPost) ∧
    stateRel sourceContinuation
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2 ∧
    codeRel continuationContext (panSemCodeAsLookup sourceContinuation.code)
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.code ∧
    excpRel continuationContext.eids sourceContinuation.exceptionShapes ∧
    localsRel continuationContext sourceContinuation.locals
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.locals := by
  let targetSlot := context.vmax + 1
  let continuationContext : PanToCrepProofContext (RiscV.Word 64) :=
    { context with
      vars := FUPDATE context.vars (name, (.one, [targetSlot]))
      vmax := context.vmax + 1 }
  let sourceContinuation : PanSemState (RiscV.Word 64) (FfiState σ) :=
    { sourceState with
      locals := updatePanValueMap sourceState.locals name (.word value)
      clock := decPanClock sourceState.clock }
  let targetCallStart : CrepRuntimeState (RiscV.Word 64) σ :=
    { targetState with
      locals := updateCrepRuntimeLocal targetState.locals targetSlot (.word 0) }
  let targetCallPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetCallStart with
      locals := updateCrepRuntimeLocal targetCallStart.locals targetSlot
        (.word value) }
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
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
      FLOOKUP_update, compileCodeRelProg, compileProgHOL, compileExpHOL] using
        htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [value]
      targetCallStart.code =
        some (.return [.var 0], fun key =>
          if key == 0 then some (.word value) else none) := by
    simp [targetCallStart, lookupCrepRuntimeCode, lookupCrepHolCode,
      htargetCodeLookup, FUPDATE_LIST]
    funext key
    by_cases hkey : key = 0
    · subst key
      simp [FUPDATE]
    · have hzero : (0 == key) = false := by simp [Ne.symm hkey]
      simp [FUPDATE, FEMPTY, hzero, hkey]
  have htargetClock : targetCallStart.clock ≠ 0 := by
    simp [targetCallStart]
    omega
  have hcallNames : ([targetSlot].eraseDups).length = 1 := by
    simp [targetSlot, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop]
  have hcallInfo : crepRuntimeCallInfoValid
      (some ([targetSlot], none) : Option (List Nat ×
        Option ((RiscV.Word 64) × CrepProg (RiscV.Word 64)))) = true := by
    simp [crepRuntimeCallInfoValid, hcallNames]
  have hwordShape : panValueShape [] (.word value) = .one := by
    simp [panValueShape]
  have hwordShapeSize : Shape.shapeSize .one = 1 := by
    exact Shape.shapeSize_one
  have hwordSize : Shape.shapeSize (panValueShape [] (.word value)) = 1 := by
    rw [hwordShape, hwordShapeSize]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 3
      targetCallStart (.call (some ([targetSlot], none)) function [.const value]) =
        some (.normal, targetCallPost) := by
    simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeCall,
      evalCrepRuntimeExps, evalCrepRuntimeExp, htargetCallLookup,
      hcallInfo, htargetClock, decCrepClock, fixCrepRuntimeClock,
      crepRuntimeCallerState, clearCrepRuntimeLocals,
      setCrepRuntimeLocalsExisting, setCrepRuntimeLocal,
      updateCrepRuntimeLocal, panTheWord, targetCallPost, targetCallStart]
    all_goals rfl
  have hlocalsPost : localsRel continuationContext sourceContinuation.locals
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.locals := by
    have hfresh := localsRelExtendNewVar context sourceState.locals
      targetState.locals (.word value) name [targetSlot] hlocals
      (by simp [hwordShape, isWfShape])
      (by simp [targetSlot])
      (by intro slot hslot
          simp only [List.mem_singleton] at hslot
          subst slot
          constructor
          · simp [targetSlot]
          · rw [hwordSize]
            simp [targetSlot])
      (by simp [hwordSize])
    have hsourceUpdate : FUPDATE sourceState.locals (name, .word value) =
        updatePanValueMap sourceState.locals name (.word value) := by
      funext key
      by_cases hkey : name = key
      · subst key
        simp [FUPDATE, updatePanValueMap]
      · simp [FUPDATE, updatePanValueMap, beq_eq_false_iff_ne.mpr hkey,
          beq_eq_false_iff_ne.mpr (Ne.symm hkey)]
    have htargetUpdate : FUPDATE_LIST targetState.locals
        ([targetSlot].zip ((panValueFlatten (.word value)).map PanWordLab.word)) =
          targetCallPost.locals := by
      funext key
      by_cases hkey : targetSlot = key
      · subst key
        simp [targetCallPost, targetSlot,
          updateCrepRuntimeLocal, FUPDATE_LIST, panValueFlatten, FUPDATE]
      · simp [targetCallPost, targetCallStart, targetSlot,
          updateCrepRuntimeLocal, FUPDATE_LIST, panValueFlatten, FUPDATE,
          beq_eq_false_iff_ne.mpr hkey]
    simpa [continuationContext, sourceContinuation, targetSlot,
      fixCrepRuntimeClock, hsourceUpdate, htargetUpdate,
      hwordShape, hwordShapeSize] using hfresh
  refine ⟨htargetRun, ?_, ?_, ?_, hlocalsPost⟩
  · simp [stateRel, fixCrepRuntimeClock, decPanClock, decCrepClock,
      hmem, hmemaddrs, hstructs,
      hshared, hglobals, hclockRel, hbe, hffi, hbase, htop]
  · exact hcode
  · exact hexcp

/-! This specialization connects the continuation composition to the actual
state-owned DecCall source evaluator. The source code entry is looked up from
`sourceState.code`; the positive-clock DecCall equation supplies the source
run, and the already-proved Tick case supplies the source-run-to-target-run
continuation IH. The target Call-prefix run and its continuation-entry
relations are the separate callee IH outputs. The target result here is the
inner `Call; Tick` segment, before the compiler's outer local-allocation
wrapper restores its temporary slot. -/
theorem panToCrepDecCallTickSourceRunComposeWithTickIH
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (fuel : Nat)
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (function name : FunName) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup sourceState.code function =
      some ([ ("parameter", .one) ],
        .return (.var .local "parameter"), .one))
    (hclock : 2 ≤ sourceState.clock)
    (targetContinuationContext : PanToCrepProofContext (RiscV.Word 64))
    (targetCallStart targetCallPost :
      CrepRuntimeState (RiscV.Word 64) σ)
    (slots : List Nat)
    (hstate : stateRel
      { sourceState with
        locals := updatePanValueMap sourceState.locals name (.word value)
        clock := decPanClock sourceState.clock }
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2)
    (hcode : codeRel targetContinuationContext
      (panSemCodeAsLookup sourceState.code)
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.code)
    (hexcp : excpRel targetContinuationContext.eids sourceState.exceptionShapes)
    (hlocals : localsRel targetContinuationContext
      (updatePanValueMap sourceState.locals name (.word value))
      (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
        (.normal, targetCallPost)).2.locals)
    (hcallPrefix :
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1)
        targetCallStart (.call (some (slots, none)) function [.const value]) =
          some (.normal, targetCallPost)) :
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi),
        decPanClock (decPanClock sourceState.clock))
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState (.decCall name .one function [.const value] .tick :
        Prog (RiscV.Word 64)) = some sourceResult ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 2)
        targetCallStart
        (.seq (.call (some (slots, none)) function [.const value])
          (compileCodeRelProg targetContinuationContext .tick)) =
            some (targetResult, targetPost) ∧
      stateRel
        (panSemCodeStateAfter
          { sourceState with
            locals := updatePanValueMap sourceState.locals name (.word value)
            clock := decPanClock sourceState.clock }
          (.control (.normal
            (updatePanValueMap sourceState.locals name (.word value))
            sourceState.globals sourceState.memory sourceState.ffi),
            decPanClock (decPanClock sourceState.clock))) targetPost ∧
      codeRel targetContinuationContext (panSemCodeAsLookup sourceState.code)
        targetPost.code ∧
      excpRel targetContinuationContext.eids sourceState.exceptionShapes ∧
      localsRel targetContinuationContext
        (updatePanValueMap sourceState.locals name (.word value)) targetPost.locals ∧
      targetResult = .normal := by
  let continuationState : PanSemState (RiscV.Word 64) (FfiState σ) :=
    { sourceState with
      locals := updatePanValueMap sourceState.locals name (.word value)
      clock := decPanClock sourceState.clock }
  let continuationResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.normal continuationState.locals continuationState.globals
      continuationState.memory continuationState.ffi),
      decPanClock continuationState.clock)
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.normal sourceState.locals sourceState.globals
      sourceState.memory sourceState.ffi),
      decPanClock (decPanClock sourceState.clock))
  let targetContinuationState : CrepRuntimeState (RiscV.Word 64) σ :=
    (fixCrepRuntimeClock (ε := FfiFinalEvent) targetCallStart
      (.normal, targetCallPost)).2
  have hcontinuationClock : continuationState.clock ≠ 0 := by
    simp [continuationState, decPanClock]
    omega
  have hsourceContinuation :
      panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
        continuationState .tick = some continuationResult := by
    have htick := panSemEvaluateCodeState_tick sourceContext
      sourcePrimitive sourceHandler panSemBitVec64BytesInWord continuationState
      (some (panSemBitVec64MemoryAccess continuationState))
    simpa [panSemEvaluateRiscV64CodeState,
      panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
      panSemBitVec64MemoryAccess, continuationState, continuationResult,
      hcontinuationClock] using htick
  have hsource :
      panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
        sourceState (.decCall name .one function [.const value] .tick :
          Prog (RiscV.Word 64)) = some sourceResult := by
    simpa [sourceResult] using
      panSemEvaluateRiscV64CodeState_decCallTick_ofEntry sourceContext
        sourcePrimitive sourceHandler sourceState function name value hentry hclock
  have hcontinuationIH := panToCrepPcCompileCorrectTickCodeStateRiscV64
    targetContinuationContext sourceContext sourcePrimitive sourceHandler
    targetHandler targetPrimitive fuel continuationState targetContinuationState
    hstate hcode hexcp hlocals
  have hIH :
      stateRel continuationState targetContinuationState →
      codeRel targetContinuationContext (panSemCodeAsLookup continuationState.code)
        targetContinuationState.code →
      excpRel targetContinuationContext.eids continuationState.exceptionShapes →
      localsRel targetContinuationContext continuationState.locals
        targetContinuationState.locals →
      panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
          continuationState .tick = some continuationResult →
        ∃ targetResult targetPost,
          evalCrepRuntimeResult targetHandler targetPrimitive (fuel + 1)
            targetContinuationState
            (compileCodeRelProg targetContinuationContext .tick) =
              some (targetResult, targetPost) ∧
          stateRel (panSemCodeStateAfter continuationState continuationResult)
            targetPost ∧
          codeRel targetContinuationContext
            (panSemCodeAsLookup
              (panSemCodeStateAfter continuationState continuationResult).code)
            targetPost.code ∧
          excpRel targetContinuationContext.eids
            (panSemCodeStateAfter continuationState continuationResult).exceptionShapes ∧
          localsRel targetContinuationContext
            (panSemCodeStateAfter continuationState continuationResult).locals
            targetPost.locals ∧
          (continuationState.clock = 0 → targetResult = .timeout) ∧
      (continuationState.clock ≠ 0 → targetResult = .normal) := by
    intro hstate' hcode' hexcp' hlocals' _hsourceRun
    have htickIH := panToCrepPcCompileCorrectTickCodeStateRiscV64
      targetContinuationContext sourceContext sourcePrimitive sourceHandler
      targetHandler targetPrimitive fuel continuationState targetContinuationState
      hstate' hcode' hexcp' hlocals'
    rcases htickIH with ⟨_hsourceTick,
      ⟨targetResult, targetPost, htargetTick, hpostState, hpostCode,
        hpostExcp, hresultZero, hresultPositive⟩⟩
    rcases hresultPositive hcontinuationClock with
      ⟨hresultNormal, hpostLocals⟩
    refine ⟨targetResult, targetPost, htargetTick, ?_, ?_, ?_, ?_,
      hresultZero, fun _ => hresultNormal⟩
    · simpa [continuationResult, hcontinuationClock] using hpostState
    · simpa [continuationResult, hcontinuationClock] using hpostCode
    · simpa [continuationResult, hcontinuationClock] using hpostExcp
    · simpa [continuationResult, hcontinuationClock] using hpostLocals
  have hsegment := panToCrepDecCallTickContinuationSeqOfSourceRunIH
    targetContinuationContext sourceContext sourcePrimitive sourceHandler
    targetHandler targetPrimitive (fuel + 1) continuationResult continuationState
    targetCallStart targetCallPost slots function
    [.const value] hsourceContinuation hstate hcode hexcp hlocals hcallPrefix
    hIH
  rcases hsegment with ⟨targetResult, targetPost, htargetSegment,
    hpostState, hpostCode, hpostExcp, hpostLocals, htargetNormal⟩
  rcases htargetNormal with ⟨_, hresultNormal⟩
  exact ⟨hsource, targetResult, targetPost, htargetSegment, hpostState,
    hpostCode, hpostExcp, hpostLocals, hresultNormal hcontinuationClock⟩

/-! Close the previous DecCall/Tick slice over a concrete `code_rel` entry.
The target Call prefix and all continuation-entry relations are derived from
the initial source/target state relation, finite state-owned source code, and
the compiled target code map; callers provide only the recursive Tick proof
boundary. -/
theorem panToCrepDecCallTickFromInitialCodeRel
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
    (hclock : 2 ≤ sourceState.clock) :
    let program : Prog (RiscV.Word 64) :=
      .decCall name .one function [.const value] .tick
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi),
        decPanClock (decPanClock sourceState.clock))
    let targetSlot := context.vmax + 1
    let continuationContext : PanToCrepProofContext (RiscV.Word 64) :=
      { context with
        vars := FUPDATE context.vars (name, (.one, [targetSlot]))
        vmax := context.vmax + 1 }
    let targetCallStart : CrepRuntimeState (RiscV.Word 64) σ :=
      { targetState with
        locals := updateCrepRuntimeLocal targetState.locals targetSlot (.word 0) }
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 4 targetCallStart
        (.seq (.call (some ([targetSlot], none)) function [.const value])
          (compileCodeRelProg continuationContext .tick)) =
            some (targetResult, targetPost) ∧
      stateRel
        (panSemCodeStateAfter
          { sourceState with
            locals := updatePanValueMap sourceState.locals name (.word value)
            clock := decPanClock sourceState.clock }
          (.control (.normal
            (updatePanValueMap sourceState.locals name (.word value))
            sourceState.globals sourceState.memory sourceState.ffi),
            decPanClock (decPanClock sourceState.clock))) targetPost ∧
      codeRel continuationContext (panSemCodeAsLookup sourceState.code)
        targetPost.code ∧
      excpRel continuationContext.eids sourceState.exceptionShapes ∧
      localsRel continuationContext
        (updatePanValueMap sourceState.locals name (.word value)) targetPost.locals ∧
      targetResult = .normal := by
  let program : Prog (RiscV.Word 64) :=
    .decCall name .one function [.const value] .tick
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.normal sourceState.locals sourceState.globals
      sourceState.memory sourceState.ffi),
      decPanClock (decPanClock sourceState.clock))
  let targetSlot := context.vmax + 1
  let continuationContext : PanToCrepProofContext (RiscV.Word 64) :=
    { context with
      vars := FUPDATE context.vars (name, (.one, [targetSlot]))
      vmax := context.vmax + 1 }
  let targetCallStart : CrepRuntimeState (RiscV.Word 64) σ :=
    { targetState with
      locals := updateCrepRuntimeLocal targetState.locals targetSlot (.word 0) }
  let targetCallPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetCallStart with
      locals := updateCrepRuntimeLocal targetCallStart.locals targetSlot
        (.word value) }
  have hprefix := panToCrepDecCallReturnParameterPrefixFromCodeRel
    context targetHandler targetPrimitive sourceState targetState function name value
    hstate hcode hexcp hlocals hentry (by omega)
  rcases hprefix with ⟨hcallPrefix, hcontinuationState, hcontinuationCode,
    hcontinuationExcp, hcontinuationLocals⟩
  have hcomposed := panToCrepDecCallTickSourceRunComposeWithTickIH
    sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive 2
    sourceState function name value hentry (by omega) continuationContext
    targetCallStart targetCallPost [targetSlot]
    hcontinuationState hcontinuationCode hcontinuationExcp
    hcontinuationLocals hcallPrefix
  simpa [program, sourceResult, targetSlot, continuationContext,
    targetCallStart, targetCallPost] using hcomposed

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

/-! Two-word continuation of the target `exp_hdl` step. This is still
Flapjack-only induction support: the handler payload occupies consecutive
return-global cells and updates the existing slots in source order. -/
theorem crepRuntimeExpHdlTwoWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (slot0 slot1 : Nat) (value0 value1 : RiscV.Word 64)
    (hvariable : FLOOKUP variables name =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslotsNe : slot0 ≠ slot1)
    (hslot0 : ∃ old, state.locals slot0 = some old)
    (hslot1 : ∃ old, state.locals slot1 = some old)
    (hglobal0 : state.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : state.globals (1 : BitVec 5) = some (.word value1)) :
    evalCrepRuntimeProg handler primitive 4 state
      (expHdlFiniteMap variables name) =
        some (.normal,
          { state with locals :=
            (updateCrepRuntimeLocal
              (updateCrepRuntimeLocal state.locals slot0 (.word value0))
              slot1 (.word value1)) }) := by
  obtain ⟨old0, hslot0⟩ := hslot0
  obtain ⟨old1, hslot1⟩ := hslot1
  have hsetup : expHdlFiniteMap (α := RiscV.Word 64) variables name =
      (.seq (.assign slot0 (.loadGlob (0 : BitVec 5)))
        (.seq (.assign slot1 (.loadGlob (1 : BitVec 5))) .skip) :
          CrepProg (RiscV.Word 64)) := by
    simp [expHdlFiniteMap, hvariable, loadGlobals, panMap2, crepNestedSeq]
  rw [hsetup]
  have hload0 : evalCrepRuntimeExp state (.loadGlob (0 : BitVec 5)) =
      some value0 := by
    simp only [evalCrepRuntimeExp]
    rw [hglobal0]
    rfl
  let stateAfterFirst :=
    { state with locals := updateCrepRuntimeLocal state.locals slot0 (.word value0) }
  let stateAfterBoth :=
    { stateAfterFirst with
      locals := updateCrepRuntimeLocal stateAfterFirst.locals slot1 (.word value1) }
  have hfirst :
      evalCrepRuntimeProg handler primitive 3 state
        (.assign slot0 (.loadGlob (0 : BitVec 5))) =
      some (.normal, stateAfterFirst) := by
    rw [evalCrepRuntimeProg]
    rw [hload0]
    rw [hslot0]
    simp only [setCrepRuntimeLocal_eq_update]
    rfl
  have hslot1Value : stateAfterFirst.locals slot1 = some old1 := by
    simp [stateAfterFirst, updateCrepRuntimeLocal, hslotsNe, hslot1]
  have hload1 :
      evalCrepRuntimeExp stateAfterFirst (.loadGlob (1 : BitVec 5)) = some value1 := by
    simp only [evalCrepRuntimeExp, stateAfterFirst]
    rw [hglobal1]
    rfl
  have hassign1 :
      evalCrepRuntimeProg handler primitive 2 stateAfterFirst
        (.assign slot1 (.loadGlob (1 : BitVec 5))) =
      some (.normal, stateAfterBoth) := by
    rw [evalCrepRuntimeProg]
    rw [hload1]
    rw [hslot1Value]
    simp only [setCrepRuntimeLocal_eq_update]
    rfl
  have hsecond :
      evalCrepRuntimeProg handler primitive 3 stateAfterFirst
        (.seq (.assign slot1 (.loadGlob (1 : BitVec 5))) .skip) =
      some (.normal, stateAfterBoth) := by
    rw [evalCrepRuntimeProg]
    rw [hassign1]
    simp [evalCrepRuntimeProg, fixCrepRuntimeClock, stateAfterBoth]
  rw [evalCrepRuntimeProg]
  rw [hfirst]
  simp only [fixCrepRuntimeClock]
  have hclockFirst : { stateAfterFirst with
      clock := min state.clock stateAfterFirst.clock } = stateAfterFirst := by
    simp [stateAfterFirst]
  rw [hclockFirst]
  rw [hsecond]

/-! Recursive target-runtime support for `exp_hdl` with an arbitrary list of
global-loaded words. This is Flapjack-only proof infrastructure; the finite-map
wrapper and arbitrary-arity handler-state relation still need to be composed
with the HOL `Call_Ret_Exception` induction hypotheses. -/
def crepRuntimeGlobalWordsRel
    (state : CrepRuntimeState (RiscV.Word 64) σ) :
    BitVec 5 → List Nat → List (RiscV.Word 64) → Prop
  | _, [], [] => True
  | address, _ :: slots, value :: values =>
      evalCrepRuntimeExp state (.loadGlob address) = some value ∧
        crepRuntimeGlobalWordsRel state (address + 1) slots values
  | _, _, _ => False

private theorem crepRuntimeGlobalWordsRel_length
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (hrel : crepRuntimeGlobalWordsRel state address slots values) :
    slots.length = values.length := by
  induction slots generalizing values address with
  | nil => cases values <;> simp [crepRuntimeGlobalWordsRel] at hrel ⊢
  | cons slot slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hrel
      | cons value values =>
          apply congrArg Nat.succ
          exact ih (address + 1) values (by
            simpa [crepRuntimeGlobalWordsRel] using hrel.2)

private theorem crepRuntimeGlobalWordsRel_updateLocal
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (slot : Nat) (value : RiscV.Word 64)
    (hglobals : crepRuntimeGlobalWordsRel state address slots values) :
    crepRuntimeGlobalWordsRel
      { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }
      address slots values := by
  induction slots generalizing values address with
  | nil => cases values <;> simp [crepRuntimeGlobalWordsRel] at hglobals ⊢
  | cons first slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hglobals
      | cons firstValue values =>
          rcases hglobals with ⟨hhead, htail⟩
          constructor
          · simpa [evalCrepRuntimeExp] using hhead
          · exact ih (address + 1) values htail

private theorem crepRuntimeExpHdlNestedWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (hslots : ∀ slot, slot ∈ slots → ∃ old, state.locals slot = some old)
    (hglobals : crepRuntimeGlobalWordsRel state address slots values) :
    evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (crepNestedSeq (panMap2 (fun destination source =>
        .assign destination source) slots
        (loadGlobals address slots.length))) =
      some (.normal,
        { state with locals := ((slots.zip values).foldl
          (fun locals (slot, value) =>
            updateCrepRuntimeLocal locals slot (.word value)) state.locals) }) := by
  induction slots generalizing state values address with
  | nil =>
      cases values with
      | nil =>
          simp [panMap2, crepNestedSeq, evalCrepRuntimeProg]
      | cons value values => simp [crepRuntimeGlobalWordsRel] at hglobals
  | cons slot slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hglobals
      | cons value values =>
          rcases hglobals with ⟨hhead, htail⟩
          obtain ⟨old, hslot⟩ := hslots slot (by simp)
          let stateAfterFirst :=
            { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }
          have hfirst :
              evalCrepRuntimeProg handler primitive (slots.length + 2) state
                (.assign slot (.loadGlob address)) =
              some (.normal, stateAfterFirst) := by
            rw [evalCrepRuntimeProg, hhead, hslot]
            simp [stateAfterFirst, setCrepRuntimeLocal_eq_update]
          have htailAfterFirst :
              crepRuntimeGlobalWordsRel stateAfterFirst (address + 1) slots values := by
            exact crepRuntimeGlobalWordsRel_updateLocal state (address + 1) slots values
              slot value htail
          have hslotsAfterFirst : ∀ tailSlot, tailSlot ∈ slots →
              ∃ current, stateAfterFirst.locals tailSlot = some current := by
            intro tailSlot htailSlot
            obtain ⟨current, hcurrent⟩ := hslots tailSlot (by simp [htailSlot])
            by_cases heq : tailSlot = slot
            · subst tailSlot
              exact ⟨.word value, by simp [stateAfterFirst, updateCrepRuntimeLocal]⟩
            · exact ⟨current, by
                simp [stateAfterFirst, updateCrepRuntimeLocal, beq_iff_eq,
                  Ne.symm heq, hcurrent]⟩
          have htailRun := ih stateAfterFirst (address + 1) values hslotsAfterFirst
            htailAfterFirst
          have hprogram :
              crepNestedSeq (panMap2 (fun destination
                  (source : CrepExp (RiscV.Word 64)) =>
                (.assign destination source : CrepProg (RiscV.Word 64))) (slot :: slots)
                (loadGlobals address (slot :: slots).length)) =
              .seq (.assign slot (.loadGlob address))
                (crepNestedSeq (panMap2 (fun destination
                    (source : CrepExp (RiscV.Word 64)) =>
                  (.assign destination source : CrepProg (RiscV.Word 64))) slots
                  (loadGlobals (address + 1) slots.length))) := by
            simp [loadGlobals, panMap2, crepNestedSeq]
          rw [hprogram, evalCrepRuntimeProg]
          have hfuel : (slot :: slots).length + 1 = slots.length + 2 := by simp
          rw [hfuel, hfirst]
          have hclock :
              fixCrepRuntimeClock (ε := FfiFinalEvent) state
                (.normal, stateAfterFirst) =
                (.normal, stateAfterFirst) := by
            simp [fixCrepRuntimeClock, stateAfterFirst]
          simp only [hclock, htailRun]
          simp [stateAfterFirst, List.zip_cons_cons, List.foldl_cons]

/-! Arbitrary-list finite-map wrapper for the target `exp_hdl` execution
above. It follows the exact flattened slot list from `FLOOKUP`; its recursive
global-word relation supplies the state-owned values read at each corresponding
return-global address. This is Flapjack-only Call induction support. -/
theorem crepRuntimeExpHdlFiniteMapWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (shape : Shape) (slots : List Nat)
    (values : List (RiscV.Word 64))
    (hvariable : FLOOKUP variables name = some (shape, slots))
    (hslots : ∀ slot, slot ∈ slots → ∃ old, state.locals slot = some old)
    (hglobals : crepRuntimeGlobalWordsRel state 0 slots values) :
    evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (expHdlFiniteMap variables name) =
      some (.normal,
        { state with locals := ((slots.zip values).foldl
          (fun locals (slot, value) =>
            updateCrepRuntimeLocal locals slot (.word value)) state.locals) }) := by
  simpa [expHdlFiniteMap, hvariable] using
    crepRuntimeExpHdlNestedWords handler primitive state 0 slots values
      hslots hglobals

/-! Relation-aware two-word target handler setup. This produces the exact
`locals_rel` premise for a handler-body IH after `exp_hdl` copies both words
from the state-owned return-global cells. -/
theorem crepRuntimeExpHdlTwoWords_localsRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (sourceLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (name : String) (slot0 slot1 : Nat)
    (old : PanValue (RiscV.Word 64)) (value0 value1 : RiscV.Word 64)
    (hlocals : localsRel context sourceLocals state.locals)
    (hsource : FLOOKUP sourceLocals name = some old)
    (hshape : panValueShape [] old = .comb [.one, .one])
    (hvariable : FLOOKUP context.vars name =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslotsNe : slot0 ≠ slot1)
    (hslot0 : ∃ current, state.locals slot0 = some current)
    (hslot1 : ∃ current, state.locals slot1 = some current)
    (hglobal0 : state.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : state.globals (1 : BitVec 5) = some (.word value1)) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive 4 state
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      localsRel context
        (FUPDATE sourceLocals
          (name, .rStruct [.word value0, .word value1])) targetPost.locals := by
  let payload : PanValue (RiscV.Word 64) := .rStruct [.word value0, .word value1]
  have hpayloadShape : panValueShape [] payload = .comb [.one, .one] := by
    simp [payload, panValueShape]
  have hshapeUpdate : panValueShape [] old = panValueShape [] payload :=
    hshape.trans hpayloadShape.symm
  obtain ⟨payloadSlots, hcontextPayload, hslotsDistinct, hlocalsPayload⟩ :=
    localsRelUpdateExistingValue context sourceLocals state.locals name old
      payload hlocals hsource hshapeUpdate
  have hpayloadSlots : payloadSlots = [slot0, slot1] := by
    have hpairs : (panValueShape [] payload, payloadSlots) =
        (.comb [.one, .one], [slot0, slot1]) :=
      Option.some.inj (hcontextPayload.symm.trans hvariable)
    exact congrArg Prod.snd hpairs
  let targetPost := { state with locals :=
    (updateCrepRuntimeLocal
      (updateCrepRuntimeLocal state.locals slot0 (.word value0))
      slot1 (.word value1)) }
  have hrun := crepRuntimeExpHdlTwoWords handler primitive state context.vars name
    slot0 slot1 value0 value1 hvariable hslotsNe hslot0 hslot1 hglobal0 hglobal1
  have hrunPost : evalCrepRuntimeProg handler primitive 4 state
      (expHdlFiniteMap context.vars name) = some (.normal, targetPost) := by
    simpa [targetPost] using hrun
  have hflat : panValueFlatten payload = [value0, value1] := by
    simp [payload, panValueFlatten, panValueFlattenValues]
  have hlocalsMap :
      FUPDATE_LIST state.locals
        (payloadSlots.zip ((panValueFlatten payload).map PanWordLab.word)) =
      targetPost.locals := by
    rw [hpayloadSlots]
    rw [hflat]
    funext slot
    simp [targetPost, FUPDATE_LIST, FUPDATE,
      updateCrepRuntimeLocal, beq_iff_eq]
  refine ⟨targetPost, hrunPost, ?_⟩
  rw [← hlocalsMap]
  exact hlocalsPayload

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

/-! The two-word counterpart supplies the full handler-body IH boundary for a
pair-shaped exception payload. The target `exp_hdl` run, code/state relations,
exception relation, and updated `locals_rel` all refer to the same actual
caller/callee states. This remains untagged Call induction support. -/
theorem crepRuntimeExpHdlTwoWords_handlerPrestateRelations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceCallerLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (targetCaller targetCallee : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (slot0 slot1 : Nat) (old : PanValue (RiscV.Word 64))
    (value0 value1 : RiscV.Word 64)
    (hstate : stateRel sourceAfterCallee targetCallee)
    (hcode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      targetCallee.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context sourceCallerLocals targetCaller.locals)
    (hsource : FLOOKUP sourceCallerLocals name = some old)
    (hshape : panValueShape [] old = .comb [.one, .one])
    (hvariable : FLOOKUP context.vars name =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslotsNe : slot0 ≠ slot1)
    (hslot0 : ∃ current, targetCaller.locals slot0 = some current)
    (hslot1 : ∃ current, targetCaller.locals slot1 = some current)
    (hglobal0 : targetCallee.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : targetCallee.globals (1 : BitVec 5) = some (.word value1)) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive 4
        (crepRuntimeCallerState targetCaller targetCallee)
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap sourceCallerLocals name
            (.rStruct [.word value0, .word value1]) }
        targetPost ∧
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      localsRel context
        (updatePanValueMap sourceCallerLocals name
          (.rStruct [.word value0, .word value1])) targetPost.locals := by
  let targetHandlerStart := crepRuntimeCallerState targetCaller targetCallee
  obtain ⟨targetPost, hrun, hlocalsPost⟩ :=
    crepRuntimeExpHdlTwoWords_localsRel context handler primitive
      targetHandlerStart sourceCallerLocals name slot0 slot1 old value0 value1
      hlocals hsource hshape hvariable hslotsNe hslot0 hslot1 hglobal0 hglobal1
  have hrunExact := crepRuntimeExpHdlTwoWords handler primitive targetHandlerStart
    context.vars name slot0 slot1 value0 value1 hvariable hslotsNe hslot0 hslot1
      hglobal0 hglobal1
  have hpostPair := Option.some.inj (hrun.symm.trans hrunExact)
  have hpost : targetPost =
      { targetHandlerStart with locals := (
        updateCrepRuntimeLocal
          (updateCrepRuntimeLocal targetHandlerStart.locals slot0 (.word value0))
          slot1 (.word value1)) } := congrArg Prod.snd hpostPair
  have hsourceUpdate :
      FUPDATE sourceCallerLocals
        (name, .rStruct [.word value0, .word value1]) =
      updatePanValueMap sourceCallerLocals name
        (.rStruct [.word value0, .word value1]) := by
    funext key
    by_cases hkey : name = key
    · subst key
      simp [FUPDATE, updatePanValueMap]
    · have hforward : (name == key) = false := beq_eq_false_iff_ne.mpr hkey
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

private theorem evalCrepRuntimeExps_eq_mapM
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (CrepExp (RiscV.Word 64))) :
    evalCrepRuntimeExps state expressions =
      expressions.mapM (evalCrepRuntimeExp state) := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps]
  | cons expression expressions ih =>
      simp [evalCrepRuntimeExps, List.mapM_cons, ih]

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

private theorem evalPanSemStateExps_member_word
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (expressions : List (Exp (RiscV.Word 64)))
    (words : List (RiscV.Word 64))
    (hsource : evalPanSemStateExps source expressions =
      some (words.map PanValue.word))
    {expression : Exp (RiscV.Word 64)}
    (hmem : expression ∈ expressions) :
    ∃ word, evalPanSemStateExp source expression = some (.word word) := by
  induction expressions generalizing words with
  | nil => simp at hmem
  | cons head tail ih =>
      cases words with
      | nil =>
          have hsourceImpossible :
              evalPanSemStateExps source (head :: tail) ≠ some [] := by
            intro h
            cases hhead : evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
                head (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
              cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
                source.globals source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord tail
                (some (panSemBitVec64MemoryAccess source)) <;>
              simp [evalPanSemStateExps, evalPanValueExps,
                evalPanValueExp.evalPanValueExps, hhead, htail] at h
          exact False.elim (hsourceImpossible (by simpa using hsource))
      | cons word words =>
          have hsource' : evalPanSemStateExps source (head :: tail) =
              some (.word word :: (words.map PanValue.word)) := by
            simpa using hsource
          obtain ⟨hhead, htail⟩ :=
            (evalPanSemStateExps_cons source head tail (.word word)
              (words.map PanValue.word)).mp hsource'
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst expression
            exact ⟨word, hhead⟩
          · exact ih words htail hmem

private theorem panValueFlatten_wordList (words : List (RiscV.Word 64)) :
    (words.map PanValue.word).flatMap panValueFlatten = words := by
  induction words with
  | nil => rfl
  | cons word words ih => simp [panValueFlatten, ih]

/-! Generic list induction for HOL `eval_map_comp_exp_flat_eq`: if every
argument satisfies the per-expression compiled-evaluation relation, successful
state-owned PanSem list evaluation lifts to production Crep evaluation of
`compileArgsHOL` and the flattened source results. The per-expression relation
is an explicit premise; this theorem does not claim its `compile_exp_val_rel`
proof for unsupported constructors or the enclosing Call theorem. -/
theorem compileArgsHOL_eval_flatten_of_each
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

/-! When every operand compiles to one word expression, HOL's `cexp_heads`
projection of `compile_exp_list` is exactly the production `compile_args`
list. This bridges the representation used by the Op constructor to the
generic list-evaluation theorem above. -/
private theorem compileExpListHOL_heads_eq_compileArgs_of_singleton
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64)))
    (hshape : ∀ expression, expression ∈ expressions →
      (compileExpHOL compilerContext expression).2 = .one)
    (hlen : ∀ expression, expression ∈ expressions →
      (compileExpHOL compilerContext expression).1.length = 1) :
    cexpHeads (expressions.map (compileExpHOL compilerContext) |>.map Prod.fst) =
      some (compileArgsHOL compilerContext expressions) := by
  induction expressions with
  | nil => simp [compileArgsHOL, cexpHeads]
  | cons expression expressions ih =>
      have hheadShape := hshape expression (by simp)
      have hheadLength := hlen expression (by simp)
      have htailShape : ∀ item, item ∈ expressions →
          (compileExpHOL compilerContext item).2 = .one := by
        intro item hmem
        exact hshape item (by simp [hmem])
      have htailLength : ∀ item, item ∈ expressions →
          (compileExpHOL compilerContext item).1.length = 1 := by
        intro item hmem
        exact hlen item (by simp [hmem])
      have htail := ih htailShape htailLength
      cases hcompiled : (compileExpHOL compilerContext expression).1 with
      | nil => simp [hcompiled] at hheadLength
      | cons head tail =>
          cases tail with
          | nil =>
              have hcompiledPair : compileExpHOL compilerContext expression =
                  ([head], .one) := by
                apply Prod.ext
                · simp [hcompiled]
                · exact hheadShape
              change cexpHeads
                ((compileExpHOL compilerContext expression).1 ::
                  (expressions.map (compileExpHOL compilerContext)).map Prod.fst) =
                some (compileArgsHOL compilerContext (expression :: expressions))
              rw [hcompiledPair]
              simp only [cexpHeads]
              rw [htail]
              simp [compileArgsHOL, hcompiledPair]
          | cons _ _ => simp [hcompiled] at hheadLength

/-! Source review of HOL `eval_map_comp_exp_flat_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1055`). Its statement
    takes `MAP (eval s) expressions = MAP SOME values`, HOL `state_rel`,
    `code_rel`, `locals_rel`, and `EVERY localised_exp expressions`, then proves
    target evaluation of all flattened `compile_exp` outputs. The theorem below
    is not that port: it quantifies production `PanSemState` and
    `CrepRuntimeState`, uses Flapjack's `stateRel`/`codeRel`/`localsRel`, and
    additionally assumes a per-expression `heach` relation containing target
    evaluation plus shape/length/well-formedness facts. Those stronger premises
    and different state/evaluator carriers change the theorem statement; the
    helper must not receive the HOL tag.

    `compileArgsHOL` is a useful flattening adapter, but it does not close this
    gap. The finite-support PanSem evaluator is now tagged; a faithful port
    still needs exact Pan-to-Crep state/context/local relations, tracked by
    `flapjack-pxn.18.3.5.8.8`. Keep bead `flapjack-4ac.5.22` open until the
    exact HOL premises and conclusion are stated and proved. -/

/-! Adapter from the complete per-expression `compile_exp_val_rel` shape to
the `compile_args` evaluator boundary. The target evaluation premise consumed
by the list induction is projected from the expression IH itself; callers do
not assume target evaluation separately. -/
theorem compileArgsHOL_eval_flatten_of_compileExpRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExps source expressions = some values)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heachEval : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    exact (heach expression hmem value heval hstate hcode hlocals
      (hlocalized expression hmem)).1
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions
      values hsource heachEval

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

/-! Exact HOL-shaped `compile_exp_val_rel` Local constructor case.  Unlike a
standalone evaluator lemma, this has the relation and localization premises
from the HOL theorem and proves all four of its conclusions for the compiler's
own output.  The target evaluation is derived from `locals_rel`; it is not an
additional induction hypothesis or premise.  This remains one constructor
case, not a port of the complete HOL induction. -/
theorem compileExpHOL_local_case_of_relations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (_hstate : stateRel source target)
    (_hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (_hlocalized : expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [])
    (hsourceEval : evalPanSemStateExp source (.var .local name) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.var .local name)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.var .local name)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 ∧
      panValueShape [] value =
        (compileExpHOL compilerContext (.var .local name)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.var .local name)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsource : FLOOKUP source.locals name = some value := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceEval
  obtain ⟨slots, hcontext, hslotsLength, htargetWords, hwf⟩ :=
    localsRelLookupCtxt context source.locals target.locals name value hlocals hsource
  have hcompiled : compileExpHOL compilerContext (.var .local name) =
      (slots.map CrepExp.var, panValueShape [] value) := by
    simp [compileExpHOL, compilerContext, hcontext]
  have htargetEval : evalCrepRuntimeExps target
      (compileExpHOL compilerContext (.var .local name)).1 =
        some (panValueFlatten value) := by
    exact compileExpHOL_local_eval_flatten context source target name value
      hlocals hsourceEval
  have hlength : (compileExpHOL compilerContext (.var .local name)).1.length =
      Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 := by
    rw [hcompiled, List.length_map, hslotsLength]
    exact panValueFlatten_length_eq_shapeSize value hwf
  have hwfCompiled : isWfShape []
      (compileExpHOL compilerContext (.var .local name)).2 = true := by
    rw [hcompiled]
    exact hwf
  exact ⟨htargetEval, hlength, by rw [hcompiled], hwfCompiled⟩

/-! A concrete `compile_args` use of the Local constructor case. This handles
argument lists consisting of local variables, deriving the complete expression
relation from `locals_rel` and then lifting it through the actual compiler
argument list. -/
theorem compileArgsHOL_localCases_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocal : ∀ expression, expression ∈ expressions →
      ∃ name, expression = .var .local name)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  apply compileArgsHOL_eval_flatten_of_compileExpRel context source target
    expressions values hstate hcode hlocals ?_ hsource ?_
  · intro expression hmem
    obtain ⟨name, rfl⟩ := hlocal expression hmem
    simp [expGlobalVars]
  · intro expression hmem value heval stateRel' codeRel' localsRel' hlocalized
    obtain ⟨name, rfl⟩ := hlocal expression hmem
    exact compileExpHOL_local_case_of_relations context source target name value
      stateRel' codeRel' localsRel' hlocalized heval

/-! `mapM` success is preserved by truncating both its input and output at the
same position. This supports `comp_field` projections of flattened locals. -/
private theorem mapM_take_of_success {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) (count : Nat)
    (hmap : inputs.mapM f = some outputs) :
    (inputs.take count).mapM f = some (outputs.take count) := by
  induction inputs generalizing outputs count with
  | nil =>
      simp only [List.mapM_nil] at hmap
      cases hmap
      simp only [List.take_nil, List.mapM_nil]
      rfl
  | cons input inputs ih =>
      cases hhead : f input with
      | none => simp [List.mapM_cons, hhead] at hmap
      | some output =>
          cases htail : inputs.mapM f with
          | none => simp [List.mapM_cons, hhead, htail] at hmap
          | some outputsTail =>
              simp [List.mapM_cons, hhead, htail] at hmap
              cases hmap
              cases count with
              | zero => simp only [List.take_zero, List.mapM_nil]; rfl
              | succ count =>
                  simp only [List.take_succ_cons]
                  simp [List.mapM_cons, hhead, ih outputsTail count htail]

private theorem mapM_drop_of_success {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) (count : Nat)
    (hmap : inputs.mapM f = some outputs) :
    (inputs.drop count).mapM f = some (outputs.drop count) := by
  induction inputs generalizing outputs count with
  | nil =>
      simp only [List.mapM_nil] at hmap
      cases hmap
      simp
  | cons input inputs ih =>
      cases hhead : f input with
      | none => simp [List.mapM_cons, hhead] at hmap
      | some output =>
          cases htail : inputs.mapM f with
          | none => simp [List.mapM_cons, hhead, htail] at hmap
          | some outputsTail =>
              simp [List.mapM_cons, hhead, htail] at hmap
              cases hmap
              cases count with
              | zero => simp [List.mapM_cons, hhead, htail]
              | succ count =>
                  simpa [List.drop_succ_cons] using ih outputsTail count htail

/-! `compile_exp_val_rel`'s RField case selects the source field's flattened
slice from the compiled inner record. This helper is the list-level bridge for
arbitrary field shapes and indices: successful target evaluation of the whole
record is projected through the same shape-sized drop/take used by
`compileField`. -/
private theorem evalCrepCompileField_panValueField
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (values : List (PanValue (RiscV.Word 64)))
    (shapes : List Shape) (expressions : List (CrepExp (RiscV.Word 64)))
    (index : Nat)
    (hshapes : shapes = values.map (panValueShape []))
    (hfieldsWf : ∀ value, value ∈ values →
      isWfShape [] (panValueShape [] value) = true)
    (hindex : index < values.length)
    (heval : evalCrepRuntimeExps target expressions =
      some (values.flatMap panValueFlatten)) :
    evalCrepRuntimeExps target (compileField index shapes expressions).1 =
      some (panValueFlatten values[index]) := by
  induction values generalizing shapes expressions index with
  | nil => simp at hindex
  | cons value values ih =>
      cases shapes with
      | nil => simp at hshapes
      | cons shape tailShapes =>
          simp only [List.map_cons] at hshapes
          cases hshapes
          have hvalueWf := hfieldsWf value (by simp)
          have hvalueSize : (panValueFlatten value).length =
              Shape.shapeSize (panValueShape [] value) :=
            panValueFlatten_length_eq_shapeSize value hvalueWf
          have heval' : evalCrepRuntimeExps target expressions =
              some (panValueFlatten value ++ values.flatMap panValueFlatten) := by
            simpa [List.flatMap_cons] using heval
          have hmapEval : expressions.mapM (evalCrepRuntimeExp target) =
              some (panValueFlatten value ++ values.flatMap panValueFlatten) := by
            simpa [evalCrepRuntimeExps_eq_mapM] using heval'
          cases index with
          | zero =>
              have hprefix := mapM_take_of_success
                (fun expression => evalCrepRuntimeExp target expression)
                expressions
                (panValueFlatten value ++ values.flatMap panValueFlatten)
                (Shape.shapeSize (panValueShape [] value))
                hmapEval
              have hprefixValues :
                  (panValueFlatten value ++ values.flatMap panValueFlatten).take
                    (Shape.shapeSize (panValueShape [] value)) =
                  panValueFlatten value := by
                rw [← hvalueSize]
                rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
              have hprefixEval : evalCrepRuntimeExps target
                  (expressions.take (Shape.shapeSize (panValueShape [] value))) =
                  some (panValueFlatten value) := by
                simpa [evalCrepRuntimeExps_eq_mapM, hprefixValues] using hprefix
              simpa [compileField] using hprefixEval
          | succ index =>
              have hindexTail : index < values.length := by simpa using hindex
              have hdrop := mapM_drop_of_success
                (fun expression => evalCrepRuntimeExp target expression)
                expressions
                (panValueFlatten value ++ values.flatMap panValueFlatten)
                (Shape.shapeSize (panValueShape [] value))
                hmapEval
              have hdropValues :
                  (panValueFlatten value ++ values.flatMap panValueFlatten).drop
                    (Shape.shapeSize (panValueShape [] value)) =
                  values.flatMap panValueFlatten := by
                rw [← hvalueSize]
                simp
              have hevalTail : evalCrepRuntimeExps target
                  (expressions.drop (Shape.shapeSize (panValueShape [] value))) =
                  some (values.flatMap panValueFlatten) := by
                simpa [evalCrepRuntimeExps_eq_mapM, hdropValues] using hdrop
              have hfieldsWfTail : ∀ item, item ∈ values →
                  isWfShape [] (panValueShape [] item) = true := by
                intro item hmem
                exact hfieldsWf item (by simp [hmem])
              have htail := ih (values.map (panValueShape []))
                (expressions.drop (Shape.shapeSize (panValueShape [] value)))
                index rfl hfieldsWfTail hindexTail hevalTail
              simpa [compileField, List.getElem_cons_succ] using htail

/-! The arbitrary-expression RField step consumes the inner expression's
compiled-evaluation IH and its shape/well-formedness facts. Source evaluation
selects the indexed field; this is the constructor step used by the enclosing
compile_exp_val_rel induction, not a standalone HOL theorem port. -/
private theorem compileExpHOL_rField_eval_flatten_ofInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (index : Nat)
    (fields : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (compiledExpressions : List (CrepExp (RiscV.Word 64)))
    (fieldShapes : List Shape)
    (hsourceInner : evalPanSemStateExp source expression =
      some (.rStruct fields))
    (hsourceField : evalPanSemStateExp source
      (.rField index expression) = some value)
    (hcompileInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expression = (compiledExpressions, .comb fieldShapes))
    (hfieldShapes : fieldShapes = fields.map (panValueShape []))
    (hfieldsWf : ∀ value, value ∈ fields →
      isWfShape [] (panValueShape [] value) = true)
    (hindex : index < fields.length)
    (hinnerIH : evalCrepRuntimeExps target compiledExpressions =
      some (fields.flatMap panValueFlatten)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).1 =
      some (panValueFlatten value) := by
  have hsourceField' : evalPanSemStateExp source
      (.rField index expression) = some fields[index] := by
    have hsourceInner' : evalPanValueExp source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.rStruct fields) := by
      simpa [evalPanSemStateExp] using hsourceInner
    simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
  have hvalue : value = fields[index] := by
    exact Option.some.inj (hsourceField.symm.trans hsourceField')
  subst value
  have hprojection := evalCrepCompileField_panValueField target fields
    fieldShapes compiledExpressions index hfieldShapes hfieldsWf hindex hinnerIH
  have hcompiledField : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      (.rField index expression) =
      compileField index fieldShapes compiledExpressions := by
    simp [compileExpHOL, hcompileInner]
  rw [hcompiledField]
  exact hprojection

/-! The RField constructor wrapper carries the HOL `compile_exp_val_rel`
inner-expression induction hypothesis: source evaluation, state/code/locals
relations, `localised_exp` (expressed here as no global variables), and the
compiled expression tuple. The IH contributes target evaluation plus the
source shape and well-formedness conclusions. -/
private theorem compileExpHOL_rField_eval_flatten_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (index : Nat)
    (fields : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (compiledExpressions : List (CrepExp (RiscV.Word 64)))
    (fieldShapes : List Shape)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceInner : evalPanSemStateExp source expression =
      some (.rStruct fields))
    (hsourceField : evalPanSemStateExp source
      (.rField index expression) = some value)
    (hindex : index < fields.length)
    (hlocalized : expGlobalVars expression = [])
    (hcompileInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expression = (compiledExpressions, .comb fieldShapes))
    (hinnerIH : evalPanSemStateExp source expression = some (.rStruct fields) →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression = (compiledExpressions, .comb fieldShapes) →
        evalCrepRuntimeExps target compiledExpressions =
            some (fields.flatMap panValueFlatten) ∧
        panValueShape [] (.rStruct fields) = .comb fieldShapes ∧
        isWfShape [] (.comb fieldShapes) = true) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).1 =
      some (panValueFlatten value) := by
  have hshapeIH := hinnerIH hsourceInner hstate hcode hlocals hlocalized hcompileInner
  rcases hshapeIH with ⟨hinnerEval, hshapeValue, hshapeWf⟩
  have hfieldShapes : fieldShapes = fields.map (panValueShape []) := by
    have hcomb : Shape.comb (fields.map (panValueShape [])) =
        Shape.comb fieldShapes := by
      simpa [panValueShape] using hshapeValue
    have hfieldShapes' : fields.map (panValueShape []) = fieldShapes := by
      injection hcomb
    exact hfieldShapes'.symm
  have hfieldsWf : ∀ field, field ∈ fields →
      isWfShape [] (panValueShape [] field) = true := by
    intro field hmem
    have hshapeMem : panValueShape [] field ∈ fieldShapes := by
      rw [hfieldShapes]
      exact List.mem_map.mpr ⟨field, hmem, rfl⟩
    exact isWfShape_of_mem (by simpa [isWfShape] using hshapeWf) hshapeMem
  exact compileExpHOL_rField_eval_flatten_ofInnerIH context source target
    expression index fields value compiledExpressions fieldShapes hsourceInner
    hsourceField hcompileInner hfieldShapes hfieldsWf hindex hinnerEval

/-! Evidence for an arbitrary-expression RField Call argument whose inner
expression is discharged by the HOL-shaped induction hypothesis. -/
inductive compileArgRFieldInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ) :
    Exp (RiscV.Word 64) → Prop where
  | rField (expression : Exp (RiscV.Word 64)) (index : Nat)
      (fields : List (PanValue (RiscV.Word 64)))
      (compiledExpressions : List (CrepExp (RiscV.Word 64)))
      (fieldShapes : List Shape)
      (hsourceInner : evalPanSemStateExp source expression =
        some (.rStruct fields))
      (hindex : index < fields.length)
      (hlocalized : expGlobalVars expression = [])
      (hcompileInner : compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression = (compiledExpressions, .comb fieldShapes))
      (hinnerIH : evalPanSemStateExp source expression = some (.rStruct fields) →
        stateRel source target →
        codeRel context (panSemCodeAsLookup source.code) target.code →
        localsRel context source.locals target.locals →
        expGlobalVars expression = [] →
        compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression = (compiledExpressions, .comb fieldShapes) →
        evalCrepRuntimeExps target compiledExpressions =
            some (fields.flatMap panValueFlatten) ∧
          panValueShape [] (.rStruct fields) = .comb fieldShapes ∧
          isWfShape [] (.comb fieldShapes) = true) :
      compileArgRFieldInnerIH context source target
        (.rField index expression)

/-! RField Call arguments with arbitrary inner expressions are lifted through
HOL `compile_args` using the exact inner-expression IH case above. This
list-level support theorem deliberately accepts only RField arguments; the
general mixed-constructor `compile_exp_val_rel` induction remains open. -/
theorem compileArgsHOL_rFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgRFieldInnerIH context source target expression)
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
    | rField inner index fields compiledExpressions fieldShapes hsourceInner
        hindex hlocalized hcompileInner hinnerIH =>
        have hsourceField : evalPanSemStateExp source
            (.rField index inner) = some fields[index] := by
          have hsourceInner' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord inner
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
            some (.rStruct fields) := by
            simpa [evalPanSemStateExp] using hsourceInner
          simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
        have hvalue : value = fields[index] := by
          exact Option.some.inj (heval.symm.trans hsourceField)
        subst value
        exact compileExpHOL_rField_eval_flatten_ofHOLIH context source target
          inner index fields fields[index] compiledExpressions fieldShapes
          hstate hcode hlocals hsourceInner hsourceField hindex hlocalized
          hcompileInner hinnerIH
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

/-! State-owned local specialization of the generic RField case above. It
handles any valid field index and any well-formed field shapes, deriving the
inner compiled evaluation from `locals_rel` rather than assuming a target run. -/
private theorem compileExpHOL_rFieldLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (index : Nat) (fields : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsource : FLOOKUP source.locals name = some (.rStruct fields))
    (hindex : index < fields.length) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index (.var .local name))).1 =
      some (panValueFlatten fields[index]) := by
  obtain ⟨slots, hcontext, _hslotsLength, htargetWords, _hvalueWf⟩ :=
    localsRelLookupCtxt context source.locals target.locals name
      (.rStruct fields) hlocals hsource
  have hcontext' : FLOOKUP context.vars name =
      some (.comb (fields.map (panValueShape [])), slots) := by
    simpa [panValueShape] using hcontext
  have hfieldsWfValues : panValueIsWfValues [] fields = true := by
    have hvalueWf := localsRelWfShape context source.locals target.locals name
      (.rStruct fields) hlocals hsource
    simpa [panValueIsWf] using hvalueWf
  have hfieldsWf : ∀ value, value ∈ fields →
      isWfShape [] (panValueShape [] value) = true := by
    intro value hmem
    obtain ⟨fieldIndex, hfieldIndex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hget : fields[fieldIndex]? = some value := by
      rw [List.getElem?_eq_getElem hfieldIndex, hvalue]
    exact panValueIsWf_isWfShape_panValueShape [] value
      (panValueIsWfValues_getElem? hfieldsWfValues hget)
  have htargetValues := mapM_panTheWord_of_wordLab target.locals slots
    (panValueFlatten (.rStruct fields)) htargetWords
  have htargetValues' : slots.mapM
      (fun slot => (target.locals slot).map panTheWord) =
      some (panValueFlatten (.rStruct fields)) := by
    simpa [FLOOKUP] using htargetValues
  have hinnerEval : evalCrepRuntimeExps target
      (slots.map CrepExp.var) = some (fields.flatMap panValueFlatten) := by
    rw [evalCrepRuntimeExps_vars_eq]
    simpa [panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using
      htargetValues'
  have hlocal : source.locals name = some (.rStruct fields) := by
    simpa [FLOOKUP] using hsource
  have hsourceInner : evalPanSemStateExp source (.var .local name) =
      some (.rStruct fields) := by
    simp [evalPanSemStateExp, evalPanValueExp, hlocal]
  have hsourceField : evalPanSemStateExp source
      (.rField index (.var .local name)) = some fields[index] := by
    simp [evalPanSemStateExp, evalPanValueExp, hlocal, hindex]
  have hcompiledInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      (.var .local name) = (slots.map CrepExp.var,
        .comb (fields.map (panValueShape []))) := by
    simp [compileExpHOL, hcontext']
  exact compileExpHOL_rField_eval_flatten_ofInnerIH context source target
    (.var .local name) index fields fields[index] (slots.map CrepExp.var)
    (fields.map (panValueShape [])) hsourceInner hsourceField hcompiledInner rfl hfieldsWf
    hindex hinnerEval

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

/-! The Const constructor base case for the four-part localized-expression
relation used by Call argument induction. This helper is Flapjack proof
infrastructure; it is not tagged as a standalone HOL theorem. -/
theorem compileExpHOL_const_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (value : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.const value) = [])
    (hsource : evalPanSemStateExp source (.const value) = some (.word value)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.const value)).1 = some [value] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).1.length = Shape.shapeSize
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.const value)).2 ∧
      panValueShape [] (.word value) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).2 = true := by
  have _ := hstate
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have hsource' := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape] at hsource' ⊢

/-! The Local constructor base case for the four-part localized-expression
relation. `locals_rel` supplies the source value's flattened target slots;
their count and value shape establish the compiler's shape conclusions. -/
theorem compileExpHOL_local_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [])
    (hsourceEval : evalPanSemStateExp source (.var .local name) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.var .local name)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.var .local name)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 ∧
      panValueShape [] value =
        (compileExpHOL compilerContext (.var .local name)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.var .local name)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsource : FLOOKUP source.locals name = some value := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceEval
  obtain ⟨slots, hcontext, hslotsLength, _htargetWords, hvalueWf⟩ :=
    localsRelLookupCtxt context source.locals target.locals name value hlocals hsource
  have heval : evalCrepRuntimeExps target
      (compileExpHOL compilerContext (.var .local name)).1 =
        some (panValueFlatten value) := by
    simpa [compilerContext] using
      compileExpHOL_local_eval_flatten context source target name value
        hlocals hsourceEval
  have hcompiled : compileExpHOL compilerContext
      (.var .local name : Exp (RiscV.Word 64)) =
      (slots.map CrepExp.var, panValueShape [] value) := by
    simp [compilerContext, compileExpHOL, hcontext]
  have hflatLength := panValueFlatten_length_eq_shapeSize value hvalueWf
  have hlen : (compileExpHOL compilerContext (.var .local name)).1.length =
      Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 := by
    rw [hcompiled]
    simpa [List.length_map] using hslotsLength.trans hflatLength
  have hshape : panValueShape [] value =
      (compileExpHOL compilerContext (.var .local name)).2 := by
    rw [hcompiled]
  have hwf : isWfShape []
      (compileExpHOL compilerContext (.var .local name)).2 = true := by
    rw [hcompiled]
    exact hvalueWf
  have _ := hstate
  have _ := hcode
  have _ := hlocalized
  exact ⟨heval, hlen, hshape, hwf⟩

/-! Full localized-expression IH cases for the two address leaves and the
    fixed RV64 word-size leaf. These support general Call-argument induction;
    they are Flapjack-only constructor proofs, not standalone HOL theorem
    ports. -/
theorem compileExpHOL_baseAddr_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.baseAddr : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .baseAddr =
      some (.word source.baseAddress)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .baseAddr).1 = some [source.baseAddress] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .baseAddr).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .baseAddr).2 ∧
      panValueShape [] (.word source.baseAddress) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .baseAddr).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .baseAddr).2 = true := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hbase, _⟩
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape, hbase]

theorem compileExpHOL_topAddr_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.topAddr : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .topAddr =
      some (.word source.topAddress)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .topAddr).1 = some [source.topAddress] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .topAddr).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .topAddr).2 ∧
      panValueShape [] (.word source.topAddress) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .topAddr).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .topAddr).2 = true := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, htop⟩
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape, htop]

theorem compileExpHOL_bytesInWord_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.bytesInWord : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .bytesInWord =
      some (.word panSemBitVec64BytesInWord)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .bytesInWord).1 =
            some [panSemBitVec64BytesInWord] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .bytesInWord).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .bytesInWord).2 ∧
      panValueShape [] (.word panSemBitVec64BytesInWord) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .bytesInWord).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .bytesInWord).2 = true := by
  have _ := hstate
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panSemBitVec64BytesInWord, CrepBytesInWord.bytesInWord,
    panValueShape, isWfShape]

/-! Under HOL `state_rel`, the source struct table is empty. PanSem therefore
    cannot successfully evaluate named-struct construction or field access.
    These full-IH cases discharge that source-inaccessible part of the
    expression induction; they do not claim named structures are supported by
    the target compiler. -/
/-! Under HOL `state_rel`, the source globals map is empty. Consequently the
Global Var constructor cannot have a successful source evaluation; the
compiler's `Const 0w` fallback is not claimed as a semantic translation. This
is the full-IH Global case, not a standalone HOL theorem port. -/
theorem compileExpHOL_global_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (_hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (_hlocals : localsRel context source.locals target.locals)
    (_hlocalized : expGlobalVars (.var .global name : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source (.var .global name) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.var .global name)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.var .global name)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.var .global name)).2 ∧
      panValueShape [] value =
        (compileExpHOL compilerContext (.var .global name)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.var .global name)).2 = true := by
  have hglobals := stateRel_globals source target hstate
  have hfalse : False := by
    simp [evalPanSemStateExp, evalPanValueExp, hglobals, FEMPTY] at hsource
  exact False.elim hfalse

theorem compileExpHOL_nStruct_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : StructName) (fields : List (FieldName × Exp (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (_hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (_hlocals : localsRel context source.locals target.locals)
    (_hlocalized : expGlobalVars (.nStruct name fields) = [])
    (hsource : evalPanSemStateExp source (.nStruct name fields) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.nStruct name fields)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.nStruct name fields)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.nStruct name fields)).2 ∧
      panValueShape [] value = (compileExpHOL compilerContext (.nStruct name fields)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.nStruct name fields)).2 = true := by
  have hstructs : source.structs = [] := stateRel_structs source target hstate
  simp [evalPanSemStateExp, evalPanValueExp, hstructs, lookupInfo] at hsource

theorem compileExpHOL_nField_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : FieldName) (expression : Exp (RiscV.Word 64))
    (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (_hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (_hlocals : localsRel context source.locals target.locals)
    (_hlocalized : expGlobalVars (.nField name expression) = [])
    (hsource : evalPanSemStateExp source (.nField name expression) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.nField name expression)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.nField name expression)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.nField name expression)).2 ∧
      panValueShape [] value = (compileExpHOL compilerContext (.nField name expression)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.nField name expression)).2 = true := by
  have hstructs : source.structs = [] := stateRel_structs source target hstate
  simp only [evalPanSemStateExp, evalPanValueExp] at hsource
  rw [hstructs] at hsource
  cases hinner : evalPanValueExp [] source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) with
  | none => simp [hinner] at hsource
  | some inner =>
      cases inner <;> simp [hinner, lookupInfo] at hsource

inductive compileArgConstOrLocal : Exp (RiscV.Word 64) → Prop where
  | const (value : RiscV.Word 64) : compileArgConstOrLocal (.const value)
  | localVar (name : String) : compileArgConstOrLocal (.var .local name)

inductive compileArgConstLocalAddress : Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstOrLocal expression) :
      compileArgConstLocalAddress expression
  | baseAddr : compileArgConstLocalAddress .baseAddr
  | topAddr : compileArgConstLocalAddress .topAddr
  | bytesInWord : compileArgConstLocalAddress .bytesInWord

private theorem compileArgConstLocalAddress_localized
    {expression : Exp (RiscV.Word 64)}
    (supported : compileArgConstLocalAddress expression) :
    expGlobalVars expression = [] := by
  cases supported with
  | existing _ supported => cases supported <;> simp [expGlobalVars]
  | baseAddr => simp [expGlobalVars]
  | topAddr => simp [expGlobalVars]
  | bytesInWord => simp [expGlobalVars]

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
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

/-! Four-conclusion localized Call-argument induction for lists of Const and
Local expressions. This composes the per-expression shape and well-formedness
facts needed by the recursive Call argument IH. -/
theorem compileArgsHOL_constOrLocal_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
        some (values.flatMap panValueFlatten) ∧
      (∀ expression, expression ∈ expressions → ∀ value,
        evalPanSemStateExp source expression = some value →
        expGlobalVars expression = [] →
        evalCrepRuntimeExps target
            (compileExpHOL compilerContext expression).1 =
              some (panValueFlatten value) ∧
          (compileExpHOL compilerContext expression).1.length =
            Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
          panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
          isWfShape [] (compileExpHOL compilerContext expression).2 = true) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    cases hsupported expression hmem <;> simp [expGlobalVars]
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
          some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval hstate' hcode' hlocals' hlocalized'
    cases hsupported expression hmem with
    | const word =>
        have hword : value = .word word := by
          have hword' : PanValue.word word = value := by
            simpa [evalPanSemStateExp, evalPanValueExp] using heval
          exact hword'.symm
        subst value
        simpa [compilerContext, panValueFlatten] using
          compileExpHOL_const_ofHOLIH context source target word
            hstate' hcode' hlocals' hlocalized' heval
    | localVar name =>
        simpa [compilerContext] using
          compileExpHOL_local_ofHOLIH context source target name value
            hstate' hcode' hlocals' hlocalized' heval
  have hcompiled := compileArgsHOL_eval_flatten_of_compileExpRel
    context source target expressions values hstate hcode hlocals hlocalized
    hsource heach
  refine ⟨?_, ?_⟩
  · simpa [compilerContext] using hcompiled
  · intro expression hmem value heval hlocalized'
    simpa [compilerContext] using
      heach expression hmem value heval hstate hcode hlocals hlocalized'

/-! Full localized-expression IH for Call arguments consisting of Const,
Local, baseAddr, topAddr, and bytesInWord. Each address case uses the fixed
RISC-V state relation; this remains a constructor subset of HOL's general
compile_exp_val_rel induction. -/
theorem compileArgsHOL_constLocalAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalAddress expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
        some (values.flatMap panValueFlatten) ∧
      (∀ expression, expression ∈ expressions → ∀ value,
        evalPanSemStateExp source expression = some value →
        expGlobalVars expression = [] →
        evalCrepRuntimeExps target
            (compileExpHOL compilerContext expression).1 =
              some (panValueFlatten value) ∧
          (compileExpHOL compilerContext expression).1.length =
            Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
          panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
          isWfShape [] (compileExpHOL compilerContext expression).2 = true) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    cases hsupported expression hmem with
    | existing _ supported => cases supported <;> simp [expGlobalVars]
    | baseAddr => simp [expGlobalVars]
    | topAddr => simp [expGlobalVars]
    | bytesInWord => simp [expGlobalVars]
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
          some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval hstate' hcode' hlocals' hlocalized'
    cases hsupported expression hmem with
    | existing expression' support =>
        cases support with
        | const word =>
            have hword : value = .word word := by
              have hword' : PanValue.word word = value := by
                simpa [evalPanSemStateExp, evalPanValueExp] using heval
              exact hword'.symm
            subst value
            simpa [compilerContext, panValueFlatten] using
              compileExpHOL_const_ofHOLIH context source target word
                hstate' hcode' hlocals' hlocalized' heval
        | localVar name =>
            simpa [compilerContext] using
              compileExpHOL_local_ofHOLIH context source target name value
                hstate' hcode' hlocals' hlocalized' heval
    | baseAddr =>
        have hvalue : value = .word source.baseAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_baseAddr_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
    | topAddr =>
        have hvalue : value = .word source.topAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_topAddr_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
    | bytesInWord =>
        have hvalue : value = .word panSemBitVec64BytesInWord := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_bytesInWord_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
  have hcompiled := compileArgsHOL_eval_flatten_of_compileExpRel
    context source target expressions values hstate hcode hlocals hlocalized
    hsource heach
  refine ⟨?_, ?_⟩
  · simpa [compilerContext] using hcompiled
  · intro expression hmem value heval hlocalized'
    simpa [compilerContext] using
      heach expression hmem value heval hstate hcode hlocals hlocalized'

private theorem compileExpHOL_constLocalAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstLocalAddress expression)
    (heval : evalPanSemStateExp source expression = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) ∧
      (compileExpHOL compilerContext expression).1.length =
        Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
      panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
      isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
  have hsourceList : evalPanSemStateExps source [expression] = some [value] := by
    exact (evalPanSemStateExps_cons source expression [] value []).mpr
      ⟨heval, by simp [evalPanSemStateExps, evalPanValueExps,
        evalPanValueExp.evalPanValueExps]⟩
  have hlistSupport : ∀ item, item ∈ [expression] →
      compileArgConstLocalAddress item := by
    intro item hmem
    have heq : item = expression := by simpa using hmem
    subst item
    exact hsupported
  obtain ⟨_, hperExpression⟩ := compileArgsHOL_constLocalAddress_ofHOLIH
    context source target [expression] [value] hstate hcode hlocals
    hlistSupport hsourceList
  exact hperExpression expression (by simp) value heval
    (compileArgConstLocalAddress_localized hsupported)

inductive compileArgConstLocalAddressOrStruct : Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalAddress expression) :
      compileArgConstLocalAddressOrStruct expression
  | rStruct (fields : List (Exp (RiscV.Word 64)))
      (supported : ∀ expression, expression ∈ fields →
        compileArgConstLocalAddress expression) :
      compileArgConstLocalAddressOrStruct (.rStruct fields)
  | loadOneConst (address : RiscV.Word 64) :
      compileArgConstLocalAddressOrStruct (.load .one (.const address))

private theorem compileArgConstLocalAddressOrStruct_localized
    {expression : Exp (RiscV.Word 64)}
    (supported : compileArgConstLocalAddressOrStruct expression) :
    expGlobalVars expression = [] := by
  cases supported with
  | existing _ supported => exact compileArgConstLocalAddress_localized supported
  | loadOneConst _ => simp [expGlobalVars]
  | rStruct fields hfields =>
      induction fields with
      | nil => simp [expGlobalVars, expGlobalVars.expGlobalVarsList]
      | cons field fields ih =>
          have hfield := compileArgConstLocalAddress_localized
            (hfields field (by simp))
          have htail : ∀ expression, expression ∈ fields →
              compileArgConstLocalAddress expression := by
            intro expression hmem
            exact hfields expression (by simp [hmem])
          have htailLocalized : expGlobalVars.expGlobalVarsList fields = [] := by
            simpa only [expGlobalVars] using ih htail
          simp only [expGlobalVars]
          simp [expGlobalVars.expGlobalVarsList, hfield, htailLocalized]

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

private theorem compileExpListHOL_map_snd_eq_map_compileExp_shape
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (fields : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext fields).map Prod.snd =
      fields.map (fun expression => (compileExpHOL compilerContext expression).2) := by
  induction fields with
  | nil => simp [compileExpHOL.compileExpListHOL]
  | cons field fields ih =>
      simp [compileExpHOL.compileExpListHOL, ih]

private theorem compileExpListHOL_map_fst_eq_map_compileExp
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext expressions).map Prod.fst =
      expressions.map (fun expression => (compileExpHOL compilerContext expression).1) := by
  induction expressions with
  | nil => simp [compileExpHOL.compileExpListHOL]
  | cons expression expressions ih =>
      simp [compileExpHOL.compileExpListHOL, ih]

/-! Full four-conclusion RStruct constructor step for localized Call
arguments. Each arbitrary field is discharged by its compile_exp_val_rel IH;
the list IHs establish source/compiled shape agreement and well-formedness,
while eval_map_comp_exp_flat_eq supplies production target evaluation. This is
induction support and does not claim the complete expression or Call theorem. -/
theorem compileExpHOL_rStruct_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (fields : List (Exp (RiscV.Word 64)))
    (fieldValues : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : ∀ expression, expression ∈ fields →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExp source (.rStruct fields) =
      some (.rStruct fieldValues))
    (heach : ∀ expression, expression ∈ fields → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.rStruct fields)).1 =
          some (panValueFlatten (.rStruct fieldValues)) ∧
      (compileExpHOL compilerContext (.rStruct fields)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.rStruct fields)).2 ∧
      panValueShape [] (.rStruct fieldValues) =
        (compileExpHOL compilerContext (.rStruct fields)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.rStruct fields)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
    simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
      evalPanValueExps] using hsource
  clear hsource
  have hfieldRel :
      fieldValues.map (panValueShape []) =
          fields.map (fun expression => (compileExpHOL compilerContext expression).2) ∧
      (∀ expression, expression ∈ fields →
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2) ∧
      (∀ expression, expression ∈ fields →
        isWfShape [] (compileExpHOL compilerContext expression).2 = true) := by
    induction fields generalizing fieldValues with
    | nil =>
        cases fieldValues with
        | nil => simp
        | cons value values =>
            simp [evalPanSemStateExps, evalPanValueExps,
              evalPanValueExp.evalPanValueExps] at hsourceFields
    | cons expression expressions ih =>
        cases fieldValues with
        | nil =>
            have hsourceImpossible :
                evalPanSemStateExps source (expression :: expressions) ≠ some [] := by
              intro h
              cases hhead : evalPanValueExp source.structs source.locals source.globals
                  source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord expression
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
                cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
                    source.globals source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord expressions
                    (some (panSemBitVec64MemoryAccess source)) <;>
                simp [evalPanSemStateExps, evalPanValueExps,
                  evalPanValueExp.evalPanValueExps, hhead, htail] at h
            exact False.elim (hsourceImpossible hsourceFields)
        | cons value values =>
            rcases (evalPanSemStateExps_cons source expression expressions value values).mp
                hsourceFields with ⟨hvalue, hvalues⟩
            have hvalueRel := heach expression (by simp) value hvalue hstate hcode
              hlocals (hlocalized expression (by simp))
            obtain ⟨_hvalueEval, hvalueLength, hvalueShape, hvalueWf⟩ := hvalueRel
            obtain ⟨hshapeTail, hlengthTail, hwfTail⟩ := ih values
              (fun item hmem => hlocalized item (by simp [hmem]))
              (fun item hmem result heval hstate' hcode' hlocals' hlocal' =>
                heach item (by simp [hmem]) result heval hstate' hcode' hlocals' hlocal')
              hvalues
            refine ⟨?_, ?_, ?_⟩
            · simp only [List.map_cons]
              rw [hvalueShape, hshapeTail]
            · intro item hmem
              rcases List.mem_cons.mp hmem with heq | htail
              · subst item
                exact hvalueLength
              · exact hlengthTail item htail
            · intro item hmem
              rcases List.mem_cons.mp hmem with heq | htail
              · subst item
                exact hvalueWf
              · exact hwfTail item htail
  have hcompiledArgs := compileArgsHOL_eval_flatten_of_compileExpRel
    context source target fields fieldValues hstate hcode hlocals hlocalized
    hsourceFields heach
  have hcompiledEval : evalCrepRuntimeExps target
      (compileExpHOL compilerContext (.rStruct fields)).1 =
        some (panValueFlatten (.rStruct fieldValues)) := by
    simpa [compilerContext, compileExpHOL,
      compileExpListHOL_flatMap_eq_compileArgsHOL, panValueFlatten_rStruct,
      panValueFlattenValues_eq_flatMap] using hcompiledArgs
  have hmapShapes := compileExpListHOL_map_snd_eq_map_compileExp_shape
    compilerContext fields
  have hcompiledShape : panValueShape [] (.rStruct fieldValues) =
      (compileExpHOL compilerContext (.rStruct fields)).2 := by
    simp only [compileExpHOL, panValueShape]
    rw [hmapShapes]
    exact congrArg Shape.comb hfieldRel.1
  have hcompiledWf : isWfShape []
      (compileExpHOL compilerContext (.rStruct fields)).2 = true := by
    simp only [compileExpHOL, isWfShape]
    rw [hmapShapes]
    apply isWfShapeList_of_all
    intro shape hshape
    obtain ⟨expression, hmem, hshape⟩ := List.mem_map.mp hshape
    subst shape
    exact hfieldRel.2.2 expression hmem
  have hcompiledLength : (compileExpHOL compilerContext (.rStruct fields)).1.length =
      Shape.shapeSize (compileExpHOL compilerContext (.rStruct fields)).2 := by
    have hEvalLength : ∀ (expressions : List (CrepExp (RiscV.Word 64)))
        (values : List (RiscV.Word 64)),
        evalCrepRuntimeExps target expressions = some values →
          values.length = expressions.length := by
      intro expressions
      induction expressions with
      | nil =>
          intro values heval
          simp [evalCrepRuntimeExps] at heval
          subst values
          rfl
      | cons expression expressions ih =>
          intro values heval
          cases hhead : evalCrepRuntimeExp target expression with
          | none => simp [evalCrepRuntimeExps, hhead] at heval
          | some head =>
              cases htail : evalCrepRuntimeExps target expressions with
              | none => simp [evalCrepRuntimeExps, hhead, htail] at heval
              | some tail =>
                  have hvalues : values = head :: tail := by
                    simpa [evalCrepRuntimeExps, hhead, htail] using heval.symm
                  subst values
                  simp [ih tail htail]
    have htargetLength := hEvalLength _ _ hcompiledEval
    have hsourceWf : isWfShape [] (panValueShape [] (.rStruct fieldValues)) = true := by
      rw [hcompiledShape]
      exact hcompiledWf
    have hflatLength := panValueFlatten_length_eq_shapeSize
      (.rStruct fieldValues) hsourceWf
    calc
      (compileExpHOL compilerContext (.rStruct fields)).1.length =
          (panValueFlatten (.rStruct fieldValues)).length := htargetLength.symm
      _ = Shape.shapeSize (panValueShape [] (.rStruct fieldValues)) := hflatLength
      _ = Shape.shapeSize (compileExpHOL compilerContext (.rStruct fields)).2 := by
        rw [hcompiledShape]
  exact ⟨by simpa [compilerContext] using hcompiledEval,
    by simpa [compilerContext] using hcompiledLength,
    by simpa [compilerContext] using hcompiledShape,
    by simpa [compilerContext] using hcompiledWf⟩

/-! Four-conclusion expression IH for one-level `RStruct` arguments whose
fields are Const/Local/address leaves, and for one-word loads from constant
addresses. The load case composes the existing HOL-shaped Load constructor
with the Const IH. -/
theorem compileExpHOL_constLocalAddressOrStruct_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstLocalAddressOrStruct expression)
    (heval : evalPanSemStateExp source expression = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) ∧
      (compileExpHOL compilerContext expression).1.length =
        Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
      panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
      isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  cases hsupported with
  | existing _ leafSupport =>
      simpa [compilerContext] using
        compileExpHOL_constLocalAddress_ofHOLIH context source target expression value
          hstate hcode hlocals leafSupport heval
  | loadOneConst address =>
      have hsourceLoad : evalPanSemStateExp source
          (.load .one (.const address)) =
          (evalCrepRuntimeExp target (.load (.const address))).map PanValue.word := by
        rcases hstate with ⟨hmemory, hdomain, _, _, _, _, _, _, _, _⟩
        simp [evalPanSemStateExp, evalPanValueExp, panValueFlatLoad,
          panValueFlatLoadFuel, panValueFlatReadWord, panSemBitVec64MemoryAccess,
          panValueMemoryAccessOfModel, evalCrepRuntimeExp, crepRuntimeLoad,
          isWfShape, hmemory, hdomain]
      rw [hsourceLoad] at heval
      cases value with
      | word loaded =>
          have htarget : evalCrepRuntimeExp target (.load (.const address)) =
              some loaded := by simpa using heval
          have hcompiled : compileExpHOL compilerContext
              (.load .one (.const address)) =
              ([.load (.const address)], .one) := by
            simp [compileExpHOL, compilerContext, loadShape,
              CrepBytesInWord.bytesInWord]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hcompiled]
            simp [evalCrepRuntimeExps, htarget, panValueFlatten]
          · rw [hcompiled]
            simp
          · rw [hcompiled]
            simp [panValueShape]
          · rw [hcompiled]
            simp [isWfShape]
      | rStruct _ => simp at heval
      | nStruct _ _ => simp at heval
  | rStruct fields hfields =>
      cases value with
      | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | rStruct fieldValues =>
          have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
            simpa [evalPanSemStateExp, evalPanValueExp, evalPanSemStateExps,
              evalPanValueExps] using heval
          have hlocalized : ∀ item, item ∈ fields → expGlobalVars item = [] := by
            intro item hmem
            exact compileArgConstLocalAddress_localized (hfields item hmem)
          have heach : ∀ item, item ∈ fields → ∀ itemValue,
              evalPanSemStateExp source item = some itemValue →
              stateRel source target →
              codeRel context (panSemCodeAsLookup source.code) target.code →
              localsRel context source.locals target.locals →
              expGlobalVars item = [] →
              evalCrepRuntimeExps target
                  (compileExpHOL compilerContext item).1 =
                    some (panValueFlatten itemValue) ∧
                (compileExpHOL compilerContext item).1.length =
                  Shape.shapeSize (compileExpHOL compilerContext item).2 ∧
                panValueShape [] itemValue = (compileExpHOL compilerContext item).2 ∧
                isWfShape [] (compileExpHOL compilerContext item).2 = true := by
            intro item hmem itemValue hitemEval hstate' hcode' hlocals' _hlocalized
            simpa [compilerContext] using
              compileExpHOL_constLocalAddress_ofHOLIH context source target item
                itemValue hstate' hcode' hlocals' (hfields item hmem) hitemEval
          simpa [compilerContext] using
            compileExpHOL_rStruct_ofHOLIH context source target fields fieldValues
              hstate hcode hlocals hlocalized heval heach
      | nStruct name namedFields =>
          simp [evalPanSemStateExp, evalPanValueExp] at heval

/-! Full argument-list IH for Const/Local/address expressions and one-level
RStructs over those leaves. This extends the argument constructors available
to the actual Call code-lookup boundary; general nested expressions remain
open. -/
theorem compileArgsHOL_constLocalAddressOrStruct_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalAddressOrStruct expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
        some (values.flatMap panValueFlatten) ∧
      (∀ expression, expression ∈ expressions → ∀ value,
        evalPanSemStateExp source expression = some value →
        expGlobalVars expression = [] →
        evalCrepRuntimeExps target
            (compileExpHOL compilerContext expression).1 =
              some (panValueFlatten value) ∧
          (compileExpHOL compilerContext expression).1.length =
            Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
          panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
          isWfShape [] (compileExpHOL compilerContext expression).2 = true) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    exact compileArgConstLocalAddressOrStruct_localized (hsupported expression hmem)
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
          some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval hstate' hcode' hlocals' _hlocalized
    simpa [compilerContext] using
      compileExpHOL_constLocalAddressOrStruct_ofHOLIH context source target
        expression value hstate' hcode' hlocals' (hsupported expression hmem) heval
  have hcompiled := compileArgsHOL_eval_flatten_of_compileExpRel
    context source target expressions values hstate hcode hlocals hlocalized hsource heach
  refine ⟨?_, ?_⟩
  · simpa [compilerContext] using hcompiled
  · intro expression hmem value heval hlocalized'
    simpa [compilerContext] using
      heach expression hmem value heval hstate hcode hlocals hlocalized'

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
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

inductive compileArgConstLocalStructAddress
    (source : PanSemState (RiscV.Word 64) (FfiState σ)) :
    Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalOrStruct expression) :
      compileArgConstLocalStructAddress source expression
  | recordFieldLocal (name : String) (index : Nat)
      (fields : List (PanValue (RiscV.Word 64)))
      (hsource : FLOOKUP source.locals name = some (.rStruct fields))
      (hindex : index < fields.length) :
      compileArgConstLocalStructAddress source
        (.rField index (.var .local name))
  | baseAddress : compileArgConstLocalStructAddress source .baseAddr
  | topAddress : compileArgConstLocalStructAddress source .topAddr
  | bytesInWord : compileArgConstLocalStructAddress source .bytesInWord

private theorem compileExpHOL_constLocalStructAddress_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstLocalStructAddress source expression)
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hbase, htop⟩
  cases hsupported with
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
          | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
          | rStruct fieldValues =>
              exact compileExpHOL_rStruct_constOrLocal_eval_flatten context source
                target fields fieldValues hlocals hfields heval
          | nStruct name fields => simp [evalPanSemStateExp, evalPanValueExp] at heval
  | recordFieldLocal name index fields hsource hindex =>
      have hlocal : source.locals name = some (.rStruct fields) := by
        simpa [FLOOKUP] using hsource
      unfold evalPanSemStateExp at heval
      simp [evalPanValueExp, hlocal, hindex] at heval
      have hvalue : value = fields[index] := heval.symm
      subst value
      exact compileExpHOL_rFieldLocal_eval_flatten context source target
        name index fields hlocals hsource hindex

/-! A source `RStruct` field may itself be an arbitrary-inner RField or one of
the already-proved Const/Local cases. This supplies the per-field case used
when a Call argument constructs a record containing a selected subrecord. -/
private theorem compileExpHOL_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstOrLocal expression ∨
      compileArgRFieldInnerIH context source target expression)
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  cases hsupported with
  | inl supported =>
      cases supported with
      | const word =>
          exact compileExpHOL_const_eval_flatten context source target word value heval
      | localVar name =>
          exact compileExpHOL_local_eval_flatten context source target name value
            hlocals heval
  | inr supported =>
      cases supported with
      | rField inner index fields compiledExpressions fieldShapes hsourceInner
          hindex hlocalized hcompileInner hinnerIH =>
        have hsourceField : evalPanSemStateExp source
            (.rField index inner) = some fields[index] := by
          have hsourceInner' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord inner
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
            some (.rStruct fields) := by
            simpa [evalPanSemStateExp] using hsourceInner
          simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
        have hvalue : value = fields[index] :=
          Option.some.inj (heval.symm.trans hsourceField)
        subst value
        exact compileExpHOL_rField_eval_flatten_ofHOLIH context source target
          inner index fields fields[index] compiledExpressions fieldShapes
          hstate hcode hlocals hsourceInner hsourceField hindex hlocalized
          hcompileInner hinnerIH

private theorem compileArgsHOL_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression ∨
        compileArgRFieldInnerIH context source target expression)
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
    exact compileExpHOL_constOrRFieldInnerIH_eval_flatten context source target
      expression value hstate hcode hlocals (hsupported expression hmem) heval
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

private theorem compileExpHOL_rStruct_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (fields : List (Exp (RiscV.Word 64)))
    (fieldValues : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ fields →
      compileArgConstOrLocal expression ∨
        compileArgRFieldInnerIH context source target expression)
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
  have hcompiled := compileArgsHOL_constOrRFieldInnerIH_eval_flatten
    context source target fields fieldValues hstate hcode hlocals hsupported
    hsourceFields
  simpa [compilerContext, compileExpHOL,
    compileExpListHOL_flatMap_eq_compileArgsHOL,
    panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled

/-! Mixed Call-argument evidence combines the already-proved constructors
with arbitrary-inner RField evidence. -/
private theorem evalPanSemStateExp_loadByte_const_riscvTarget
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.loadByte (.const address)) =
      (evalCrepRuntimeExp (riscvCrepWordTarget target)
        (.loadByte (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, hbe, _, _, _⟩
  have hmemoryView : panValueWordMemory source.memory =
      crepRuntimeMemoryView target.memory := by
    funext query
    simp [panValueWordMemory, crepRuntimeMemoryView, hmemory]
  have hread :
      panModelReadByte panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be =
        panModelReadByte (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian := by
    rw [← hdomain, ← hmemoryView, ← hbe]
    cases source.be with
    | false =>
        simp [panModelReadByte, panSemBitVec64WordModel,
          RiscV.panRiscVMemoryModelForEndian, RiscV.panRiscVMemoryModel,
          RiscV.panRiscVGetByteEndian, RiscV.panRiscVGetByte,
          panSemBitVec64BytesInWord]
    | true =>
        have hindex : ∀ index : Nat, 8 - index - 1 = 7 - index := by
          intro index
          omega
        simp [panModelReadByte, panSemBitVec64WordModel,
          RiscV.panRiscVMemoryModelForEndian, RiscV.panRiscVMemoryModel,
          RiscV.panRiscVGetByteEndian, RiscV.panRiscVGetByte,
          panSemBitVec64BytesInWord, hindex]
  calc
    evalPanSemStateExp source (.loadByte (.const address)) =
        (panModelReadByte panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be).map
            PanValue.word := by
      simp [evalPanSemStateExp, evalPanValueExp,
        panSemBitVec64MemoryAccess,
        panValueMemoryAccessOfModel, panSemBitVec64BytesInWord]
    _ = (panModelReadByte (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian).map PanValue.word := by
      rw [hread]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget target)
          (.loadByte (.const address))).map PanValue.word := by
      simp [evalCrepRuntimeExp, crepRuntimeLoadByte_wordTarget_eq_riscv]

private theorem evalPanSemStateExp_load32_const_riscvTarget
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.load32 (.const address)) =
      (evalCrepRuntimeExp (riscvCrepWordTarget target)
        (.load32 (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, hbe, _, _, _⟩
  have hmemoryView : panValueWordMemory source.memory =
      crepRuntimeMemoryView target.memory := by
    funext query
    simp [panValueWordMemory, crepRuntimeMemoryView, hmemory]
  have hread :
      panModelRead32 panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be =
        panModelRead32 (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian := by
    rw [← hdomain, ← hmemoryView, ← hbe]
    cases source.be with
    | false =>
        simp [panModelRead32, panSemBitVec64WordModel,
          panSemBitVec64BytesInWord, RiscV.panRiscVMemoryModelForEndian,
          RiscV.panRiscVMemoryModel, RiscV.panRiscVGetByteEndian,
          RiscV.panRiscVGetByte, RiscV.panRiscVByteIndex]
    | true =>
        have hindex : ∀ index : Nat, 8 - index - 1 = 7 - index := by
          intro index
          omega
        simp [panModelRead32, panSemBitVec64WordModel,
        panSemBitVec64BytesInWord, RiscV.panRiscVMemoryModelForEndian,
        RiscV.panRiscVMemoryModel, RiscV.panRiscVGetByteEndian,
        RiscV.panRiscVGetByte, RiscV.panRiscVByteIndex, hindex]
  calc
    evalPanSemStateExp source (.load32 (.const address)) =
        (panModelRead32 panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be).map
            PanValue.word := by
      simp [evalPanSemStateExp, evalPanValueExp,
        panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
        panSemBitVec64BytesInWord]
    _ = (panModelRead32 (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian).map PanValue.word := by
      rw [hread]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget target)
          (.load32 (.const address))).map PanValue.word := by
      simp [evalCrepRuntimeExp, crepRuntimeLoad32_wordTarget_eq_riscv]

private theorem evalPanSemStateExp_loadOne_const_stateRel
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.load .one (.const address)) =
      (evalCrepRuntimeExp target (.load (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, _, _, _, _⟩
  simp [evalPanSemStateExp, evalPanValueExp, panValueFlatLoad,
    panValueFlatLoadFuel, panValueFlatReadWord, panSemBitVec64MemoryAccess,
    panValueMemoryAccessOfModel, evalCrepRuntimeExp, crepRuntimeLoad,
    isWfShape, hmemory, hdomain]

private theorem evalPanSemStateExp_loadTwo_const_stateRel
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source
        (.load (.comb [.one, .one]) (.const address)) =
      ((evalCrepRuntimeExp target (.load (.const address))).bind fun first =>
        (evalCrepRuntimeExp target (.load (.const (address + 8)))).map fun second =>
          .rStruct [.word first, .word second]) := by
  rcases hstate with ⟨hmemory, hdomain, _, hstructs, _, _, _, _, _, _⟩
  simp [evalPanSemStateExp, evalPanValueExp, panValueFlatLoad,
    panValueFlatLoadFuel, panValueFlatLoadListFuel, panValueFlatReadWord,
    panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
    panValueFlatContextFuel, panValueFlatShapeFuel,
    panValueFlatShapeFuel.panValueFlatShapeListFuel,
    evalCrepRuntimeExp, crepRuntimeLoad, panValueFlatOffset,
    shapeSizeWithContext, panSemBitVec64BytesInWord,
    isWfShape, isWfShape.isWfShapeList, hmemory, hdomain, hstructs]
  cases target.memaddrs address <;>
    cases target.memaddrs (address + 8) <;>
    simp

/-! Restricted, untagged Call-argument induction evidence. In addition to the
existing Const/Local, record, address, byte-load, and word-load cases, this
relation now admits a two-word flat Load only at a constant address and under
the canonical RISC-V target invariant. This is argument-evaluation support;
it does not establish the complete HOL `compile_exp_val_rel` induction. -/
inductive compileArgConstLocalStructAddressOrRFieldInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ) :
    Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddress source expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression
  | rField (expression : Exp (RiscV.Word 64)) (index : Nat)
      (supported : compileArgRFieldInnerIH context source target
        (.rField index expression)) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rField index expression)
  | rStructRField (fields : List (Exp (RiscV.Word 64)))
      (hfields : ∀ expression, expression ∈ fields →
        compileArgConstOrLocal expression ∨
          compileArgRFieldInnerIH context source target expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rStruct fields)
  | rStructNested (fields : List (Exp (RiscV.Word 64)))
      (hfields : ∀ expression, expression ∈ fields →
        compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rStruct fields)
  | globalVar (name : String) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.var .global name)
  | baseAddr :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .baseAddr
  | topAddr :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .topAddr
  | bytesInWord :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .bytesInWord
  | nStruct (name : String) (fields : List (FieldName × Exp (RiscV.Word 64))) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.nStruct name fields)
  | nField (name : FieldName) (expression : Exp (RiscV.Word 64)) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.nField name expression)
  | loadByteConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte (.const address))
  | load32ConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 (.const address))
  | loadOneConst (address : RiscV.Word 64) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load .one (.const address))
  | loadTwoConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load (.comb [.one, .one]) (.const address))
  | load32LocalCanonicalTarget (name : String) (slot : Nat)
      (hvariable : FLOOKUP context.vars name = some (.one, [slot]))
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 (.var .local name))
  | loadByteLocalCanonicalTarget (name : String) (slot : Nat)
      (hvariable : FLOOKUP context.vars name = some (.one, [slot]))
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte (.var .local name))
  | loadByteSupportedAddress (address : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddressOrRFieldInnerIH
        context source target address)
      (hshape : (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax } address).2 = .one)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte address)
  | load32SupportedAddress (address : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddressOrRFieldInnerIH
        context source target address)
      (hshape : (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax } address).2 = .one)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 address)
  | panOpMul (left right : Exp (RiscV.Word 64))
      (hleft : compileArgConstLocalStructAddressOrRFieldInnerIH context source target left)
      (hright : compileArgConstLocalStructAddressOrRFieldInnerIH context source target right) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.panOp .mul [left, right])

private theorem evalCrepRuntimeExps_length_of_some
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (CrepExp (RiscV.Word 64)))
    (values : List (RiscV.Word 64))
    (heval : evalCrepRuntimeExps state expressions = some values) :
    values.length = expressions.length := by
  induction expressions generalizing values with
  | nil => simp [evalCrepRuntimeExps] at heval; subst values; rfl
  | cons expression expressions ih =>
      cases hhead : evalCrepRuntimeExp state expression with
      | none => simp [evalCrepRuntimeExps, hhead] at heval
      | some head =>
          cases htail : evalCrepRuntimeExps state expressions with
          | none => simp [evalCrepRuntimeExps, hhead, htail] at heval
          | some tail =>
              have hvalues : values = head :: tail := by
                simpa [evalCrepRuntimeExps, hhead, htail] using heval.symm
              subst values
              simp [ih tail htail]

private theorem compileField_shape_eq_panValueField
    (fields : List (PanValue (RiscV.Word 64))) (index : Nat)
    (expressions : List (CrepExp (RiscV.Word 64)))
    (hindex : index < fields.length) :
    (compileField index (fields.map (panValueShape [])) expressions).2 =
      panValueShape [] fields[index] := by
  induction fields generalizing index expressions with
  | nil => simp at hindex
  | cons field fields ih =>
      cases index with
      | zero => simp [compileField]
      | succ index =>
          have hindex' : index < fields.length := by simpa using hindex
          simpa [compileField, List.getElem_cons_succ] using
            ih index (expressions.drop (Shape.shapeSize (panValueShape [] field))) hindex'

/-! The complete four-conclusion RField step for HOL-shaped expression
induction. It projects the source field from the `RStruct` result and uses the
inner full IH's compiled tuple, source shape, target evaluation, and Wf facts
to establish the actual `compileField` output relation. -/
theorem compileExpHOL_rField_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (index : Nat)
    (fields : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (compiledExpressions : List (CrepExp (RiscV.Word 64)))
    (fieldShapes : List Shape)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceInner : evalPanSemStateExp source expression = some (.rStruct fields))
    (hsourceField : evalPanSemStateExp source (.rField index expression) = some value)
    (hindex : index < fields.length)
    (hlocalized : expGlobalVars expression = [])
    (hcompileInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expression = (compiledExpressions, .comb fieldShapes))
    (hinnerIH : evalPanSemStateExp source expression = some (.rStruct fields) →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression = (compiledExpressions, .comb fieldShapes) →
      evalCrepRuntimeExps target compiledExpressions =
          some (fields.flatMap panValueFlatten) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length = Shape.shapeSize
            (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] (.rStruct fields) = .comb fieldShapes ∧
        isWfShape [] (.comb fieldShapes) = true) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.rField index expression)).1 = some (panValueFlatten value) ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.rField index expression)).2 ∧
      panValueShape [] value = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hshapeIH := hinnerIH hsourceInner hstate hcode hlocals hlocalized hcompileInner
  rcases hshapeIH with ⟨hinnerEval, _hinnerLength, hshapeValue, hshapeWf⟩
  have hfieldShapes : fieldShapes = fields.map (panValueShape []) := by
    have hcomb : Shape.comb (fields.map (panValueShape [])) = Shape.comb fieldShapes := by
      simpa [panValueShape] using hshapeValue
    have heq : fields.map (panValueShape []) = fieldShapes := by injection hcomb
    exact heq.symm
  have hsourceField' : evalPanSemStateExp source (.rField index expression) =
      some fields[index] := by
    have hinner : evalPanValueExp source.structs source.locals source.globals
        source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
        expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
        some (.rStruct fields) := by simpa [evalPanSemStateExp] using hsourceInner
    simp [evalPanSemStateExp, evalPanValueExp, hinner, hindex]
  have hvalue : value = fields[index] :=
    Option.some.inj (hsourceField.symm.trans hsourceField')
  have hfieldsWf : ∀ field, field ∈ fields →
      isWfShape [] (panValueShape [] field) = true := by
    intro field hmem
    have hshapeMem : panValueShape [] field ∈ fieldShapes := by
      rw [hfieldShapes]
      exact List.mem_map.mpr ⟨field, hmem, rfl⟩
    exact isWfShape_of_mem (by simpa [isWfShape] using hshapeWf) hshapeMem
  have heval := compileExpHOL_rField_eval_flatten_ofInnerIH
    context source target expression index fields value compiledExpressions fieldShapes
    hsourceInner hsourceField hcompileInner hfieldShapes hfieldsWf hindex hinnerEval
  have hcompileOut : compileExpHOL compilerContext (.rField index expression) =
      compileField index fieldShapes compiledExpressions := by
    simp only [compileExpHOL]
    rw [hcompileInner]
  have houtShape : (compileExpHOL compilerContext (.rField index expression)).2 =
      panValueShape [] value := by
    rw [hcompileOut, hfieldShapes]
    rw [hvalue]
    exact compileField_shape_eq_panValueField fields index compiledExpressions hindex
  have hlength := evalCrepRuntimeExps_length_of_some target
    (compileExpHOL compilerContext (.rField index expression)).1
    (panValueFlatten value) heval
  have hvalueWf : isWfShape [] (panValueShape [] value) = true := by
    rw [hvalue]
    exact hfieldsWf fields[index] (List.getElem_mem hindex)
  have hflatLength := panValueFlatten_length_eq_shapeSize value hvalueWf
  refine ⟨heval, ?_, ?_, ?_⟩
  · calc
      (compileExpHOL compilerContext (.rField index expression)).1.length =
          (panValueFlatten value).length := hlength.symm
      _ = Shape.shapeSize (panValueShape [] value) := hflatLength
      _ = Shape.shapeSize (compileExpHOL compilerContext (.rField index expression)).2 := by
        rw [← houtShape]
  · exact houtShape.symm
  · rw [houtShape]
    exact hvalueWf

private theorem compileArgConstLocalStructAddressOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    {expression : Exp (RiscV.Word 64)}
    (evidence : compileArgConstLocalStructAddressOrRFieldInnerIH
      context source target expression)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  revert value
  induction evidence with
  | existing expression supported =>
      intro value heval
      exact compileExpHOL_constLocalStructAddress_eval_flatten context source
        target expression value hstate hlocals supported heval
  | rField inner index supported =>
      cases supported with
      | rField _ _ fields compiledExpressions fieldShapes hsourceInner
          hindex hlocalized hcompileInner hinnerIH =>
        intro value heval
        have hsourceField : evalPanSemStateExp source
            (.rField index inner) = some fields[index] := by
          have hsourceInner' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord inner
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
            some (.rStruct fields) := by
            simpa [evalPanSemStateExp] using hsourceInner
          simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
        have hvalue : value = fields[index] :=
          Option.some.inj (heval.symm.trans hsourceField)
        subst value
        exact compileExpHOL_rField_eval_flatten_ofHOLIH context source target
          inner index fields fields[index] compiledExpressions fieldShapes
          hstate hcode hlocals hsourceInner hsourceField hindex hlocalized
          hcompileInner hinnerIH
  | rStructRField fields hfields =>
      intro value heval
      cases value with
      | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | nStruct name values => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | rStruct fieldValues =>
          exact compileExpHOL_rStruct_constOrRFieldInnerIH_eval_flatten
            context source target fields fieldValues hstate hcode hlocals
            hfields heval
  | rStructNested fields hfields ih =>
      intro value heval
      cases value with
      | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | nStruct name values => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | rStruct fieldValues =>
          have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
            simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
              evalPanValueExps] using heval
          let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
          have heach : ∀ field, field ∈ fields → ∀ fieldValue,
              evalPanSemStateExp source field = some fieldValue →
              evalCrepRuntimeExps target
                (compileExpHOL compilerContext field).1 =
                  some (panValueFlatten fieldValue) := by
            intro field hmem fieldValue hfield
            exact ih field hmem fieldValue hfield
          have hcompiled := compileArgsHOL_eval_flatten_of_each compilerContext
            source target fields fieldValues hsourceFields heach
          simpa [compilerContext, compileExpHOL,
            compileExpListHOL_flatMap_eq_compileArgsHOL,
            panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled
  | globalVar name =>
      intro value heval
      have hglobals := stateRel_globals source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hglobals, FEMPTY] at heval
  | baseAddr =>
      intro value heval
      have hsource : evalPanSemStateExp source .baseAddr =
          some (.word source.baseAddress) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word source.baseAddress :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_baseAddr_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | topAddr =>
      intro value heval
      have hsource : evalPanSemStateExp source .topAddr =
          some (.word source.topAddress) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word source.topAddress :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_topAddr_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | bytesInWord =>
      intro value heval
      have hsource : evalPanSemStateExp source .bytesInWord =
          some (.word panSemBitVec64BytesInWord) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word panSemBitVec64BytesInWord :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_bytesInWord_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | nStruct name fields =>
      intro value heval
      have hstructs := stateRel_structs source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hstructs, lookupInfo] at heval
  | nField name expression =>
      intro value heval
      have hstructs := stateRel_structs source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hstructs, lookupInfo] at heval
      simp only [Option.bind_eq_some_iff] at heval
      rcases heval with ⟨innerValue, _, hresult⟩
      cases innerValue <;> simp at hresult
  | loadByteConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.loadByte (.const address)) =
        (evalCrepRuntimeExp target (.loadByte (.const address))).map PanValue.word := by
        simpa [hcanonical.symm] using hsourceTarget
      rw [hsourceTarget'] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target
              (.loadByte (.const address)) = some word := by
            simpa using heval
          simp [compileExpHOL, evalCrepRuntimeExps, panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | load32ConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.load32 (.const address)) =
        (evalCrepRuntimeExp target (.load32 (.const address))).map PanValue.word := by
        simpa [hcanonical.symm] using hsourceTarget
      rw [hsourceTarget'] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target
              (.load32 (.const address)) = some word := by
            simpa using heval
          simp [compileExpHOL, evalCrepRuntimeExps, panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | loadOneConst address =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadOne_const_stateRel
        source target address hstate
      rw [hsourceTarget] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target (.load (.const address)) =
              some word := by
            simpa using heval
          let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
          have hcompiled : compileExpHOL compilerContext
              (.load .one (.const address)) =
              ([.load (.const address)], .one) := by
            simp [compileExpHOL, compilerContext, loadShape,
              CrepBytesInWord.bytesInWord]
          simp [compilerContext, hcompiled, evalCrepRuntimeExps,
            panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | loadTwoConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadTwo_const_stateRel
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.load (.comb [.one, .one]) (.const address)) =
        (evalCrepRuntimeExp target (.load (.const address))).bind fun first =>
          (evalCrepRuntimeExp target
            (.load (.const (address + 8)))).map fun second =>
              .rStruct [.word first, .word second] := by
        simpa [hcanonical.symm] using hsourceTarget
      have haddressOffset : address + (8 : RiscV.Word 64) =
          address + BitVec.ofNat 64 8 := by rfl
      rw [haddressOffset] at hsourceTarget'
      rw [hsourceTarget'] at heval
      cases hfirst : evalCrepRuntimeExp target (.load (.const address)) with
      | none => simp [hfirst] at heval
      | some first =>
          cases hsecond : evalCrepRuntimeExp target
              (.load (.const (address + BitVec.ofNat 64 8))) with
          | none => simp [hsecond] at heval
          | some second =>
              have hvalue : value = .rStruct [.word first, .word second] := by
                have hequality :
                    some (.rStruct [.word first, .word second]) = some value := by
                  simpa [hfirst, hsecond] using heval
                exact (Option.some.inj hequality).symm
              subst value
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hcompiledLoad :
                  compileExpHOL compilerContext
                    (.load (.comb [.one, .one]) (.const address)) =
                    ([.load (.const address),
                      .load (.op .add
                        [.const address, .const (BitVec.ofNat 64 8)])],
                      .comb [.one, .one]) := by
                simp [compileExpHOL, compilerContext, loadShape,
                  CrepBytesInWord.bytesInWord, Shape.shapeSize]
              have htargetAddressNext :
                  evalCrepRuntimeExp target
                    (.op .add
                      [.const address, .const (BitVec.ofNat 64 8)]) =
                    some (address + 8) := by
                have hwordArgs :
                    ([.const address, .const (BitVec.ofNat 64 8)] :
                      List (CrepExp (RiscV.Word 64))).mapM
                        (evalCrepRuntimeExp (riscvCrepWordTarget target)) =
                      some [address, 8] := by
                  simp [evalCrepRuntimeExp]
                have hwordResult :
                    (([.const address, .const (BitVec.ofNat 64 8)] :
                      List (CrepExp (RiscV.Word 64))).mapM
                        (evalCrepRuntimeExp (riscvCrepWordTarget target))).bind
                        (wordOpHOL .add) = some (address + 8) := by
                  rw [hwordArgs]
                  simp [wordOpHOL, wordOp]
                rw [hcanonical]
                rw [evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
                exact hwordResult
              have htargetRun :
                  evalCrepRuntimeExps target
                      (compileExpHOL compilerContext
                        (.load (.comb [.one, .one]) (.const address))).1 =
                    some [first, second] := by
                rw [hcompiledLoad]
                have hloadBind (expression : CrepExp (RiscV.Word 64)) :
                    evalCrepRuntimeExp target (.load expression) =
                      (evalCrepRuntimeExp target expression).bind
                        (crepRuntimeLoad target) := by
                  simp only [evalCrepRuntimeExp]
                  rfl
                have hcompiledSecond : evalCrepRuntimeExp target
                    (.load (.op .add
                      [.const address, .const (BitVec.ofNat 64 8)])) = some second := by
                  rw [hloadBind, htargetAddressNext]
                  have hsecondLoad : crepRuntimeLoad target
                      (address + 8) = some second := by
                    simpa [evalCrepRuntimeExp] using hsecond
                  exact hsecondLoad
                simp [evalCrepRuntimeExps, hfirst, hcompiledSecond]
              simpa [compilerContext, panValueFlatten, panValueFlattenValues] using
                htargetRun
  | load32LocalCanonicalTarget name slot hvariable hcanonical =>
      intro value heval
      cases haddressValue : evalPanSemStateExp source (.var .local name) with
      | none =>
          have hlocal : source.locals name = none := by
            simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
          simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
      | some addressValue =>
          cases addressValue with
          | word address =>
              have hlocal : source.locals name = some (.word address) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              have hsourceConst :
                  evalPanSemStateExp source (.load32 (.var .local name)) =
                    evalPanSemStateExp source (.load32 (.const address)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hlocal]
              have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
                source target address hstate
              have hsourceTarget' : evalPanSemStateExp source
                  (.load32 (.const address)) =
                (evalCrepRuntimeExp target (.load32 (.const address))).map
                  PanValue.word := by
                simpa [hcanonical.symm] using hsourceTarget
              have hcompiledLocal := compileExpHOL_local_eval_flatten context
                source target name (.word address) hlocals haddressValue
              have htargetVariable :
                  evalCrepRuntimeExp target (.var slot) = some address := by
                have hmap : evalCrepRuntimeExps target [.var slot] =
                    some [address] := by
                  simpa [compileExpHOL, hvariable, panValueFlatten] using
                    hcompiledLocal
                cases hvalue : evalCrepRuntimeExp target (.var slot) with
                | none => simp [evalCrepRuntimeExps, hvalue] at hmap
                | some word =>
                    have hword : word = address := by
                      simpa [evalCrepRuntimeExps, hvalue] using hmap
                    simp [hword]
              have htargetLoad :
                  evalCrepRuntimeExp target (.load32 (.var slot)) =
                    evalCrepRuntimeExp target (.load32 (.const address)) := by
                simp [evalCrepRuntimeExp, htargetVariable]
              have hcompiled :
                  (compileExpHOL
                    { vars := context.vars, funcs := context.funcs,
                      eids := context.eids, vmax := context.vmax }
                    (.load32 (.var .local name))).1 = [.load32 (.var slot)] := by
                simp [compileExpHOL, hvariable]
              rw [hsourceConst, hsourceTarget'] at heval
              cases value with
              | word word =>
                  have htarget :
                      evalCrepRuntimeExp target (.load32 (.const address)) =
                        some word := by
                    simpa using heval
                  simp [hcompiled, evalCrepRuntimeExps,
                    htargetLoad, htarget, panValueFlatten]
              | rStruct fields => simp at heval
              | nStruct name fields => simp at heval
          | rStruct fields =>
              have hlocal : source.locals name = some (.rStruct fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
          | nStruct structName fields =>
              have hlocal : source.locals name = some (.nStruct structName fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
  | loadByteLocalCanonicalTarget name slot hvariable hcanonical =>
      intro value heval
      cases haddressValue : evalPanSemStateExp source (.var .local name) with
      | none =>
          have hlocal : source.locals name = none := by
            simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
          simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
      | some addressValue =>
          cases addressValue with
          | word address =>
              have hlocal : source.locals name = some (.word address) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              have hsourceConst :
                  evalPanSemStateExp source (.loadByte (.var .local name)) =
                    evalPanSemStateExp source (.loadByte (.const address)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hlocal]
              have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
                source target address hstate
              have hsourceTarget' : evalPanSemStateExp source
                  (.loadByte (.const address)) =
                (evalCrepRuntimeExp target (.loadByte (.const address))).map
                  PanValue.word := by
                simpa [hcanonical.symm] using hsourceTarget
              have hcompiledLocal := compileExpHOL_local_eval_flatten context
                source target name (.word address) hlocals haddressValue
              have htargetVariable :
                  evalCrepRuntimeExp target (.var slot) = some address := by
                have hmap : evalCrepRuntimeExps target [.var slot] =
                    some [address] := by
                  simpa [compileExpHOL, hvariable, panValueFlatten] using
                    hcompiledLocal
                cases hvalue : evalCrepRuntimeExp target (.var slot) with
                | none => simp [evalCrepRuntimeExps, hvalue] at hmap
                | some word =>
                    have hword : word = address := by
                      simpa [evalCrepRuntimeExps, hvalue] using hmap
                    simp [hword]
              have htargetLoad :
                  evalCrepRuntimeExp target (.loadByte (.var slot)) =
                    evalCrepRuntimeExp target (.loadByte (.const address)) := by
                simp [evalCrepRuntimeExp, htargetVariable]
              have hcompiled :
                  (compileExpHOL
                    { vars := context.vars, funcs := context.funcs,
                      eids := context.eids, vmax := context.vmax }
                    (.loadByte (.var .local name))).1 = [.loadByte (.var slot)] := by
                simp [compileExpHOL, hvariable]
              rw [hsourceConst, hsourceTarget'] at heval
              cases value with
              | word word =>
                  have htarget :
                      evalCrepRuntimeExp target (.loadByte (.const address)) =
                        some word := by
                    simpa using heval
                  simp [hcompiled, evalCrepRuntimeExps,
                    htargetLoad, htarget, panValueFlatten]
              | rStruct fields => simp at heval
              | nStruct name fields => simp at heval
          | rStruct fields =>
              have hlocal : source.locals name = some (.rStruct fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
          | nStruct structName fields =>
              have hlocal : source.locals name = some (.nStruct structName fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
  | loadByteSupportedAddress address supported hshape hcanonical ihAddress =>
      intro value heval
      cases haddress : evalPanSemStateExp source address with
      | none =>
          have hsourceAddress :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using haddress
          simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
      | some addressValue =>
          cases addressValue with
          | word addressWord =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word addressWord) := by
                simpa [evalPanSemStateExp] using haddress
              have hsourceByte :
                  evalPanSemStateExp source (.loadByte address) =
                    evalPanSemStateExp source (.loadByte (.const addressWord)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress]
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hshape' : (compileExpHOL compilerContext address).2 = .one := by
                simpa [compilerContext] using hshape
              have hcompiledAddressRun :
                  evalCrepRuntimeExps target
                    (compileExpHOL compilerContext address).1 = some [addressWord] := by
                simpa [panValueFlatten] using ihAddress (.word addressWord) haddress
              have hcompiledAddressLength :
                  (compileExpHOL compilerContext address).1.length = 1 := by
                simpa using (evalCrepRuntimeExps_length_of_some target
                  (compileExpHOL compilerContext address).1 [addressWord]
                  hcompiledAddressRun).symm
              cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
              | nil => simp [hcompiledAddress] at hcompiledAddressLength
              | cons targetAddress targetAddressTail =>
                  cases targetAddressTail with
                  | nil =>
                      have hcompiledAddressSingleton :
                          (compileExpHOL compilerContext address).1 =
                            [targetAddress] := by
                        simp [hcompiledAddress]
                      have hcompiledAddressPair :
                          compileExpHOL compilerContext address =
                            ([targetAddress], .one) := by
                        apply Prod.ext
                        · exact hcompiledAddressSingleton
                        · exact hshape'
                      have htargetAddress :
                          evalCrepRuntimeExp target targetAddress = some addressWord := by
                        rw [hcompiledAddressSingleton] at hcompiledAddressRun
                        cases hvalue : evalCrepRuntimeExp target targetAddress with
                        | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
                        | some word =>
                            have hword : word = addressWord := by
                              simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                            simp [hword]
                      have hcompiledLoad :
                          (compileExpHOL compilerContext (.loadByte address)).1 =
                            [.loadByte targetAddress] := by
                        simp only [compileExpHOL, hcompiledAddressPair]
                      have htargetLoad :
                          evalCrepRuntimeExp target (.loadByte targetAddress) =
                            evalCrepRuntimeExp target (.loadByte (.const addressWord)) := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
                        source target addressWord hstate
                      have hsourceTarget' :
                          evalPanSemStateExp source
                            (.loadByte (.const addressWord)) =
                            (evalCrepRuntimeExp target
                              (.loadByte (.const addressWord))).map PanValue.word := by
                        simpa [hcanonical.symm] using hsourceTarget
                      rw [hsourceByte, hsourceTarget'] at heval
                      cases value with
                      | word resultWord =>
                          have htarget : evalCrepRuntimeExp target
                              (.loadByte (.const addressWord)) = some resultWord := by
                            simpa using heval
                          simp [compilerContext, hcompiledLoad,
                            evalCrepRuntimeExps, htargetLoad, htarget,
                            panValueFlatten]
                      | rStruct fields => simp at heval
                      | nStruct name fields => simp at heval
                  | cons _ _ => simp [hcompiledAddress] at hcompiledAddressLength
          | rStruct fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.rStruct fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
          | nStruct name fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.nStruct name fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
  | load32SupportedAddress address supported hshape hcanonical ihAddress =>
      intro value heval
      cases haddress : evalPanSemStateExp source address with
      | none =>
          have hsourceAddress :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using haddress
          simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
      | some addressValue =>
          cases addressValue with
          | word addressWord =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word addressWord) := by
                simpa [evalPanSemStateExp] using haddress
              have hsourceConst :
                  evalPanSemStateExp source (.load32 address) =
                    evalPanSemStateExp source (.load32 (.const addressWord)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress]
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hshape' : (compileExpHOL compilerContext address).2 = .one := by
                simpa [compilerContext] using hshape
              have hcompiledAddressRun :
                  evalCrepRuntimeExps target
                    (compileExpHOL compilerContext address).1 = some [addressWord] := by
                simpa [panValueFlatten] using
                  ihAddress (.word addressWord) haddress
              have hcompiledAddressLength :
                  (compileExpHOL compilerContext address).1.length = 1 := by
                simpa using (evalCrepRuntimeExps_length_of_some target
                  (compileExpHOL compilerContext address).1 [addressWord]
                  hcompiledAddressRun).symm
              cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
              | nil => simp [hcompiledAddress] at hcompiledAddressLength
              | cons targetAddress targetAddressTail =>
                  cases targetAddressTail with
                  | nil =>
                      have hcompiledAddressSingleton :
                          (compileExpHOL compilerContext address).1 =
                            [targetAddress] := by
                        simp [hcompiledAddress]
                      have hcompiledAddressPair :
                          compileExpHOL compilerContext address =
                            ([targetAddress], .one) := by
                        apply Prod.ext
                        · exact hcompiledAddressSingleton
                        · exact hshape'
                      have htargetAddress :
                          evalCrepRuntimeExp target targetAddress =
                            some addressWord := by
                        rw [hcompiledAddressSingleton] at hcompiledAddressRun
                        cases hvalue : evalCrepRuntimeExp target targetAddress with
                        | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
                        | some word =>
                            have hword : word = addressWord := by
                              simpa [evalCrepRuntimeExps, hvalue] using
                                hcompiledAddressRun
                            simp [hword]
                      have hcompiledLoad :
                          (compileExpHOL compilerContext (.load32 address)).1 =
                            [.load32 targetAddress] := by
                        simp only [compileExpHOL, hcompiledAddressPair]
                      have htargetLoad :
                          evalCrepRuntimeExp target (.load32 targetAddress) =
                            evalCrepRuntimeExp target (.load32 (.const addressWord)) := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
                        source target addressWord hstate
                      have hsourceTarget' :
                          evalPanSemStateExp source
                            (.load32 (.const addressWord)) =
                            (evalCrepRuntimeExp target
                              (.load32 (.const addressWord))).map PanValue.word := by
                        simpa [hcanonical.symm] using hsourceTarget
                      rw [hsourceConst, hsourceTarget'] at heval
                      cases value with
                      | word resultWord =>
                          have htarget :
                              evalCrepRuntimeExp target
                                (.load32 (.const addressWord)) = some resultWord := by
                            simpa using heval
                          simp [compilerContext, hcompiledLoad,
                            evalCrepRuntimeExps, htargetLoad, htarget,
                            panValueFlatten]
                      | rStruct fields => simp at heval
                      | nStruct name fields => simp at heval
                  | cons _ _ => simp [hcompiledAddress] at hcompiledAddressLength
          | rStruct fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.rStruct fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
          | nStruct name fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.nStruct name fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
  | panOpMul left right hleft hright ihLeft ihRight =>
      intro value heval
      have hevalSource : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          (.panOp .mul [left, right])
          (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some value := by
        simpa [evalPanSemStateExp] using heval
      cases hleftValue : evalPanSemStateExp source left with
      | none =>
          have hleftValue' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord left
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hleftValue
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue'] at hevalSource
      | some leftValue =>
          have hleftValue' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord left
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some leftValue := by
            simpa [evalPanSemStateExp] using hleftValue
          cases hrightValue : evalPanSemStateExp source right with
          | none =>
              have hrightValue' : evalPanValueExp source.structs source.locals
                  source.globals source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord right
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
                simpa [evalPanSemStateExp] using hrightValue
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue', hrightValue'] at hevalSource
          | some rightValue =>
              have hrightValue' : evalPanValueExp source.structs source.locals
                  source.globals source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord right
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some rightValue := by
                simpa [evalPanSemStateExp] using hrightValue
              cases leftValue with
              | word leftWord =>
                  cases rightValue with
                  | word rightWord =>
                      have hcomputed : evalPanValueExp source.structs source.locals
                          source.globals source.memory source.baseAddress source.topAddress
                          panSemBitVec64BytesInWord (.panOp .mul [left, right])
                          (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                            some (.word (leftWord * rightWord)) := by
                        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                          hleftValue', hrightValue', evalPanOp]
                      have hvalue : value = .word (leftWord * rightWord) :=
                        Option.some.inj (hevalSource.symm.trans hcomputed)
                      subst value
                      let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                        { vars := context.vars, funcs := context.funcs,
                          eids := context.eids, vmax := context.vmax }
                      have hleftRun : evalCrepRuntimeExps target
                          (compileExpHOL compilerContext left).1 = some [leftWord] := by
                        simpa [panValueFlatten] using
                          ihLeft (.word leftWord) hleftValue
                      have hrightRun : evalCrepRuntimeExps target
                          (compileExpHOL compilerContext right).1 = some [rightWord] := by
                        simpa [panValueFlatten] using
                          ihRight (.word rightWord) hrightValue
                      have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
                        simpa using (evalCrepRuntimeExps_length_of_some target
                          (compileExpHOL compilerContext left).1 [leftWord] hleftRun).symm
                      have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
                        simpa using (evalCrepRuntimeExps_length_of_some target
                          (compileExpHOL compilerContext right).1 [rightWord] hrightRun).symm
                      cases hleftCompiled : (compileExpHOL compilerContext left).1 with
                      | nil => simp [hleftCompiled] at hleftLength
                      | cons leftExpression leftTail =>
                          cases leftTail with
                          | nil =>
                              have hleftSingleton :
                                  (compileExpHOL compilerContext left).1 = [leftExpression] := by
                                simp [hleftCompiled]
                              have hleftExpressionRun :
                                  evalCrepRuntimeExp target leftExpression = some leftWord := by
                                rw [hleftSingleton] at hleftRun
                                cases hword : evalCrepRuntimeExp target leftExpression with
                                | none => simp [evalCrepRuntimeExps, hword] at hleftRun
                                | some word =>
                                    have hwordEq : word = leftWord := by
                                      simpa [evalCrepRuntimeExps, hword] using hleftRun
                                    simp [hwordEq]
                              cases hrightCompiled : (compileExpHOL compilerContext right).1 with
                              | nil => simp [hrightCompiled] at hrightLength
                              | cons rightExpression rightTail =>
                                  cases rightTail with
                                  | nil =>
                                      have hrightSingleton :
                                          (compileExpHOL compilerContext right).1 =
                                            [rightExpression] := by
                                        simp [hrightCompiled]
                                      have hrightExpressionRun :
                                          evalCrepRuntimeExp target rightExpression =
                                            some rightWord := by
                                        rw [hrightSingleton] at hrightRun
                                        cases hword : evalCrepRuntimeExp target rightExpression with
                                        | none => simp [evalCrepRuntimeExps, hword] at hrightRun
                                        | some word =>
                                            have hwordEq : word = rightWord := by
                                              simpa [evalCrepRuntimeExps, hword] using hrightRun
                                            simp [hwordEq]
                                      have hcompiled :
                                          (compileExpHOL compilerContext
                                            (.panOp .mul [left, right])).1 =
                                            [.crepOp .mul [leftExpression, rightExpression]] := by
                                        simp [compileExpHOL,
                                          compileExpHOL.compileExpListHOL,
                                          hleftSingleton, hrightSingleton,
                                          cexpHeads, compilePanOp]
                                      simp [compilerContext, hcompiled, evalCrepRuntimeExps,
                                        evalCrepRuntimeExp, crepOpCrep, hleftExpressionRun,
                                        hrightExpressionRun, panValueFlatten]
                                  | cons _ _ => simp [hrightCompiled] at hrightLength
                          | cons _ _ => simp [hleftCompiled] at hleftLength
                  | rStruct _ =>
                      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                        hleftValue', hrightValue', evalPanOp] at hevalSource
                  | nStruct _ _ =>
                      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                        hleftValue', hrightValue', evalPanOp] at hevalSource
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue', hrightValue', evalPanOp] at hevalSource
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue', hrightValue', evalPanOp] at hevalSource

/-! The LoadByte constructor of HOL `compile_exp_val_rel`, specialized to the
fixed RISC-V target, consumes the complete relation for its localized address
expression. This remains induction support rather than a standalone HOL port. -/
theorem compileExpHOL_loadByte_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source (.loadByte address) =
      some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.loadByte address)).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.loadByte address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.loadByte address)).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.loadByte address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.loadByte address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceAddress : evalPanSemStateExp source address =
      some (.word addressWord) := haddress
  have haddressRel := haddressIH (.word addressWord) hsourceAddress
    hstate hcode hlocals haddressLocalized
  have haddressShape :
      (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.loadByte address) =
                ([.loadByte targetAddress], .one) := by
            simp only [compileExpHOL, hcompiledAddressPair]
          have htargetLoad :
              evalCrepRuntimeExp target (.loadByte targetAddress) =
                evalCrepRuntimeExp target (.loadByte (.const addressWord)) := by
            simp [evalCrepRuntimeExp, htargetAddress]
          have hsourceLoadConst :
              evalPanSemStateExp source (.loadByte address) =
                evalPanSemStateExp source (.loadByte (.const addressWord)) := by
            have hsourceAddressEval :
                evalPanValueExp source.structs source.locals source.globals
                  source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord address
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                    some (.word addressWord) := by
              simpa [evalPanSemStateExp] using hsourceAddress
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
            source target addressWord hstate
          have hsourceTarget' :
              evalPanSemStateExp source (.loadByte (.const addressWord)) =
                (evalCrepRuntimeExp target
                  (.loadByte (.const addressWord))).map PanValue.word := by
            simpa [hcanonical.symm] using hsourceTarget
          rw [hsourceLoadConst, hsourceTarget'] at hsourceLoad
          have htargetLoadResult : evalCrepRuntimeExp target
              (.loadByte (.const addressWord)) = some loaded := by
            simpa using hsourceLoad
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [compilerContext, hcompiledLoad, evalCrepRuntimeExps,
              htargetLoad, htargetLoadResult]
          · simp [compilerContext, hcompiledLoad]
          · simp [compilerContext, hcompiledLoad, panValueShape]
          · simp [compilerContext, hcompiledLoad, isWfShape]
      | cons _ _ => simp [hcompiledAddress] at haddressLength

/-! The Load32 constructor of HOL `compile_exp_val_rel`, specialized to the
fixed RISC-V target, consumes the complete relation for its localized address
expression. Its explicit canonical-target hypothesis is not a premise of the
general HOL theorem; discharging it from the eventual state relation remains
open. This remains induction support rather than a standalone HOL port. -/
theorem compileExpHOL_load32_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source (.load32 address) =
      some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load32 address)).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load32 address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load32 address)).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load32 address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load32 address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceAddress : evalPanSemStateExp source address =
      some (.word addressWord) := haddress
  have haddressRel := haddressIH (.word addressWord) hsourceAddress
    hstate hcode hlocals haddressLocalized
  have haddressShape :
      (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.load32 address) =
                ([.load32 targetAddress], .one) := by
            simp only [compileExpHOL, hcompiledAddressPair]
          have htargetLoad :
              evalCrepRuntimeExp target (.load32 targetAddress) =
                evalCrepRuntimeExp target (.load32 (.const addressWord)) := by
            simp [evalCrepRuntimeExp, htargetAddress]
          have hsourceLoadConst :
              evalPanSemStateExp source (.load32 address) =
                evalPanSemStateExp source (.load32 (.const addressWord)) := by
            have hsourceAddressEval :
                evalPanValueExp source.structs source.locals source.globals
                  source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord address
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                    some (.word addressWord) := by
              simpa [evalPanSemStateExp] using hsourceAddress
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
            source target addressWord hstate
          have hsourceTarget' :
              evalPanSemStateExp source (.load32 (.const addressWord)) =
                (evalCrepRuntimeExp target
                  (.load32 (.const addressWord))).map PanValue.word := by
            simpa [hcanonical.symm] using hsourceTarget
          rw [hsourceLoadConst, hsourceTarget'] at hsourceLoad
          have htargetLoadResult : evalCrepRuntimeExp target
              (.load32 (.const addressWord)) = some loaded := by
            simpa using hsourceLoad
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [compilerContext, hcompiledLoad, evalCrepRuntimeExps,
              htargetLoad, htargetLoadResult]
          · simp [compilerContext, hcompiledLoad]
          · simp [compilerContext, hcompiledLoad, panValueShape]
          · simp [compilerContext, hcompiledLoad, isWfShape]
      | cons _ _ => simp [hcompiledAddress] at haddressLength


/-! Full localized-expression IH case for a one-word generic Load. It uses
the source-owned memory evaluator and `stateRel` to match production target
`Load`; larger shapes still require a recursive flattened-memory proof. -/
theorem compileExpHOL_loadOne_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source (.load .one address) =
      some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load .one address)).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load .one address)).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have haddressRel := haddressIH (.word addressWord) haddress
    hstate hcode hlocals haddressLocalized
  have haddressShape : (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.load .one address) =
                ([.load targetAddress], .one) := by
            simp [compileExpHOL, compilerContext, hcompiledAddressPair,
              loadShape, CrepBytesInWord.bytesInWord]
          have htargetLoad : evalCrepRuntimeExp target (.load targetAddress) =
              evalCrepRuntimeExp target (.load (.const addressWord)) := by
            simp [evalCrepRuntimeExp, htargetAddress]
          have hsourceAddressEval :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                  some (.word addressWord) := by
            simpa [evalPanSemStateExp] using haddress
          have hsourceLoadConst :
              evalPanSemStateExp source (.load .one address) =
                evalPanSemStateExp source (.load .one (.const addressWord)) := by
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_loadOne_const_stateRel
            source target addressWord hstate
          rw [hsourceLoadConst, hsourceTarget] at hsourceLoad
          have htargetLoadResult :
              evalCrepRuntimeExp target (.load (.const addressWord)) =
                some loaded := by
            simpa using hsourceLoad
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [compilerContext, hcompiledLoad, evalCrepRuntimeExps,
              htargetLoad, htargetLoadResult]
          · simp [compilerContext, hcompiledLoad]
          · simp [compilerContext, hcompiledLoad, panValueShape]
          · simp [compilerContext, hcompiledLoad, isWfShape]
      | cons _ _ => simp [hcompiledAddress] at haddressLength


/-! Full localized-expression IH case for a two-word flat Load. The proof
keeps the source flat-load stride and target compile_exp load_shape stride
aligned at the fixed RV64 width. Arbitrary shape lists remain open. -/
theorem compileExpHOL_loadTwo_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded0 loaded1 : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcanonical : target = riscvCrepWordTarget target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source
      (.load (.comb [.one, .one]) address) =
        some (.rStruct [.word loaded0, .word loaded1])) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) address)).1 = some [loaded0, loaded1] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load (.comb [.one, .one]) address)).2 ∧
      panValueShape [] (.rStruct [.word loaded0, .word loaded1]) =
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have haddressRel := haddressIH (.word addressWord) haddress
    hstate hcode hlocals haddressLocalized
  have haddressShape : (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.load (.comb [.one, .one]) address) =
                ([.load targetAddress,
                  .load (.op .add [targetAddress, .const 8])], .comb [.one, .one]) := by
            simp only [compileExpHOL, compilerContext, hcompiledAddressPair,
              CrepBytesInWord.bytesInWord]
            apply Prod.ext
            · have hcount : Shape.shapeSize (.comb [.one, .one]) = 2 := by
                simp [Shape.shapeSize]
              rw [hcount]
              change loadShape (0 : RiscV.Word 64)
                (BitVec.ofNat 64 (64 / 8)) 2 targetAddress =
                [.load targetAddress,
                  .load (.op .add [targetAddress, .const 8])]
              rw [loadShape]
              rw [loadShape]
              rfl
            · rfl
          have htargetAddressNext :
              evalCrepRuntimeExp target (.op .add [targetAddress, .const 8]) =
                some (addressWord + 8) := by
            have htargetAddressCanonical :
                evalCrepRuntimeExp (riscvCrepWordTarget target) targetAddress =
                  some addressWord := by
              rw [hcanonical] at htargetAddress
              exact htargetAddress
            have hwordArgs :
                [targetAddress, .const 8].mapM
                    (evalCrepRuntimeExp (riscvCrepWordTarget target)) =
                  some [addressWord, 8] := by
              simp only [List.mapM_cons, List.mapM_nil,
                evalCrepRuntimeExp, htargetAddressCanonical]
              rfl
            have hwordResult :
                ([targetAddress, .const 8].mapM
                    (evalCrepRuntimeExp (riscvCrepWordTarget target))).bind
                    (wordOpHOL .add) = some (addressWord + 8) := by
              rw [hwordArgs]
              simp [wordOpHOL, wordOp]
            rw [hcanonical]
            rw [evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
            exact hwordResult
          have hsourceAddressEval :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                  some (.word addressWord) := by
            simpa [evalPanSemStateExp] using haddress
          have hsourceLoadConst :
              evalPanSemStateExp source (.load (.comb [.one, .one]) address) =
                evalPanSemStateExp source
                  (.load (.comb [.one, .one]) (.const addressWord)) := by
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_loadTwo_const_stateRel
            source target addressWord hstate
          rw [hsourceLoadConst, hsourceTarget] at hsourceLoad
          cases hfirst : evalCrepRuntimeExp target (.load (.const addressWord)) with
          | none => simp [hfirst] at hsourceLoad
          | some first =>
              simp only [hfirst, Option.bind_some] at hsourceLoad
              cases hsecond : evalCrepRuntimeExp target
                  (.load (.const (addressWord + 8))) with
              | none =>
                  simp only [hsecond, Option.map_none] at hsourceLoad
                  cases hsourceLoad
              | some second =>
                  simp only [hsecond, Option.map_some] at hsourceLoad
                  have hstruct := Option.some.inj hsourceLoad
                  have hvalues := PanValue.rStruct.inj hstruct
                  have hfirstValue : first = loaded0 := by
                    injection hvalues with hhead htail
                    exact PanValue.word.inj hhead
                  have hsecondValue : second = loaded1 := by
                    injection hvalues with hhead htail
                    injection htail with hheadSecond hnil
                    exact PanValue.word.inj hheadSecond
                  have hcompiledFirstLoad :
                      evalCrepRuntimeExp target (.load targetAddress) =
                        some loaded0 := by
                    have hfirstLoad := hfirst
                    calc
                      evalCrepRuntimeExp target (.load targetAddress) =
                          crepRuntimeLoad target addressWord := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      _ = evalCrepRuntimeExp target (.load (.const addressWord)) := by
                        simp [evalCrepRuntimeExp]
                      _ = some first := hfirst
                      _ = some loaded0 := by rw [hfirstValue]
                  have hcompiledSecondLoad :
                      evalCrepRuntimeExp target
                        (.load (.op .add [targetAddress, .const 8])) =
                        some loaded1 := by
                    have hloadBind (expression : CrepExp (RiscV.Word 64)) :
                        evalCrepRuntimeExp target (.load expression) =
                          (evalCrepRuntimeExp target expression).bind
                            (crepRuntimeLoad target) := by
                      simp only [evalCrepRuntimeExp]
                      rfl
                    rw [hloadBind, htargetAddressNext]
                    have hsecondLoad : crepRuntimeLoad target
                        (addressWord + 8) = some second := by
                      simpa [evalCrepRuntimeExp] using hsecond
                    exact hsecondLoad.trans (congrArg some hsecondValue)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · have htargetRun : evalCrepRuntimeExps target
                        ([.load targetAddress,
                          .load (.op .add [targetAddress, .const 8])] :
                            List (CrepExp (RiscV.Word 64))) =
                          some [loaded0, loaded1] := by
                      change evalCrepRuntimeExps target
                        ([.load targetAddress] ++
                          [.load (.op .add [targetAddress, .const 8])]) =
                        some ([loaded0] ++ [loaded1])
                      have hfirstList : evalCrepRuntimeExps target
                          [.load targetAddress] = some [loaded0] := by
                        simp [evalCrepRuntimeExps, hcompiledFirstLoad]
                      have hsecondList : evalCrepRuntimeExps target
                          [.load (.op .add [targetAddress, .const 8])] =
                            some [loaded1] := by
                        simp only [evalCrepRuntimeExps, hcompiledSecondLoad]
                        simp
                      exact evalCrepRuntimeExps_append target
                        [.load targetAddress]
                        [.load (.op .add [targetAddress, .const 8])]
                        [loaded0] [loaded1]
                        hfirstList hsecondList
                    simpa [compilerContext, hcompiledLoad] using htargetRun
                  · simp [compilerContext, hcompiledLoad, Shape.shapeSize]
                  · simp [compilerContext, hcompiledLoad, panValueShape]
                  · simp [compilerContext, hcompiledLoad, isWfShape,
                      isWfShape.isWfShapeList]
      | cons _ _ => simp [hcompiledAddress] at haddressLength


/-! Regression corollaries compose the generic flat-load expression IH with a
localized variable address. They keep the address nonconstant and verify that
the recursive address IH, source state, and exact target load path compose for
both one-word and two-word loads. These are untagged induction support. -/
theorem compileExpHOL_loadOne_localAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load .one (.var .local name)) = some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load .one (.var .local name))).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load .one (.var .local name))).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).2 = true := by
  have haddress : evalPanSemStateExp source (.var .local name) =
      some (.word addressWord) := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceLocal
  have haddressIH : ∀ addressValue,
      evalPanSemStateExp source (.var .local name) = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.var .local name)).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              (.var .local name)).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 = true := by
    intro (addressValue : PanValue (RiscV.Word 64)) hvalue hstate' hcode' hlocals' hlocalized'
    have hvalue' : addressValue = .word addressWord :=
      Option.some.inj (hvalue.symm.trans haddress)
    subst addressValue
    exact compileExpHOL_local_ofHOLIH context source target name
      (.word addressWord) hstate' hcode' hlocals' hlocalized' haddress
  exact compileExpHOL_loadOne_ofHOLIH context source target
    (.var .local name) addressWord loaded hstate hcode hlocals
    (by simp [expGlobalVars]) haddress haddressIH hsourceLoad

theorem compileExpHOL_loadTwo_localAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (addressWord loaded0 loaded1 : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcanonical : target = riscvCrepWordTarget target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load (.comb [.one, .one]) (.var .local name)) =
        some (.rStruct [.word loaded0, .word loaded1])) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) (.var .local name))).1 =
          some [loaded0, loaded1] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) (.var .local name))).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load (.comb [.one, .one]) (.var .local name))).2 ∧
      panValueShape [] (.rStruct [.word loaded0, .word loaded1]) =
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) (.var .local name))).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) (.var .local name))).2 = true := by
  have haddress : evalPanSemStateExp source (.var .local name) =
      some (.word addressWord) := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceLocal
  have haddressIH : ∀ addressValue,
      evalPanSemStateExp source (.var .local name) = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.var .local name)).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              (.var .local name)).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 = true := by
    intro (addressValue : PanValue (RiscV.Word 64)) hvalue hstate' hcode' hlocals' hlocalized'
    have hvalue' : addressValue = .word addressWord :=
      Option.some.inj (hvalue.symm.trans haddress)
    subst addressValue
    exact compileExpHOL_local_ofHOLIH context source target name
      (.word addressWord) hstate' hcode' hlocals' hlocalized' haddress
  exact compileExpHOL_loadTwo_ofHOLIH context source target
    (.var .local name) addressWord loaded0 loaded1 hstate hcanonical hcode hlocals
    (by simp [expGlobalVars]) haddress haddressIH hsourceLoad


/-! The Cmp constructor case for a full localized-expression IH, at the fixed
RISC-V target. This is induction support for the HOL expression relation; the
enclosing Call simulation remains open. -/
theorem compileExpHOL_cmp_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Cmp) (left right : Exp (RiscV.Word 64))
    (leftWord rightWord result : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (hleftLocalized : expGlobalVars left = [])
    (hrightLocalized : expGlobalVars right = [])
    (hleftSource : evalPanSemStateExp source left = some (.word leftWord))
    (hrightSource : evalPanSemStateExp source right = some (.word rightWord))
    (hleftIH : ∀ value,
      evalPanSemStateExp source left = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars left = [] →
      evalCrepRuntimeExps target (compileExpHOL
        (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
        left).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) left).1.length =
            Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
              context.funcs context.vmax context.eids) left).2 ∧
        panValueShape [] value = (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) left).2 ∧
        isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) left).2 = true)
    (hrightIH : ∀ value,
      evalPanSemStateExp source right = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars right = [] →
      evalCrepRuntimeExps target (compileExpHOL
        (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
        right).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) right).1.length =
            Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
              context.funcs context.vmax context.eids) right).2 ∧
        panValueShape [] value = (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) right).2 ∧
        isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) right).2 = true)
    (hsourceCmp : evalPanSemStateExp source (.cmp operator left right) =
      some (.word result)) :
    evalCrepRuntimeExps target (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.cmp operator left right)).1 = some [result] ∧
    (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs context.vmax
      context.eids)
      (.cmp operator left right)).1.length = Shape.shapeSize
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs context.vmax
          context.eids)
          (.cmp operator left right)).2 ∧
    panValueShape [] (.word result) = (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.cmp operator left right)).2 ∧
    isWfShape [] (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.cmp operator left right)).2 = true := by
  let compilerContext :=
    panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids
  have hleftRel := hleftIH (.word leftWord) hleftSource hstate hcode hlocals
    hleftLocalized
  have hrightRel := hrightIH (.word rightWord) hrightSource hstate hcode hlocals
    hrightLocalized
  have hleftShape : (compileExpHOL compilerContext left).2 = .one := by
    have h := hleftRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have hrightShape : (compileExpHOL compilerContext right).2 = .one := by
    have h := hrightRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have hleftRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext left).1 = some [leftWord] := by
    simpa [compilerContext, panValueFlatten] using hleftRel.1
  have hrightRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext right).1 = some [rightWord] := by
    simpa [compilerContext, panValueFlatten] using hrightRel.1
  have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
    have h := hleftRel.2.1
    rw [hleftShape] at h
    simpa using h
  have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
    have h := hrightRel.2.1
    rw [hrightShape] at h
    simpa using h
  cases hleftCompiled : (compileExpHOL compilerContext left).1 with
  | nil => simp [hleftCompiled] at hleftLength
  | cons leftExpression leftTail =>
      cases leftTail with
      | nil =>
          have hleftSingleton : (compileExpHOL compilerContext left).1 =
              [leftExpression] := by simp [hleftCompiled]
          have hleftPair : compileExpHOL compilerContext left =
              ([leftExpression], .one) := by
            apply Prod.ext
            · exact hleftSingleton
            · exact hleftShape
          have hleftTarget : evalCrepRuntimeExp target leftExpression =
              some leftWord := by
            rw [hleftSingleton] at hleftRun
            cases hvalue : evalCrepRuntimeExp target leftExpression with
            | none => simp [evalCrepRuntimeExps, hvalue] at hleftRun
            | some word =>
                have heq : word = leftWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hleftRun
                simp [heq]
          cases hrightCompiled : (compileExpHOL compilerContext right).1 with
          | nil => simp [hrightCompiled] at hrightLength
          | cons rightExpression rightTail =>
              cases rightTail with
              | nil =>
                  have hrightSingleton : (compileExpHOL compilerContext right).1 =
                      [rightExpression] := by simp [hrightCompiled]
                  have hrightPair : compileExpHOL compilerContext right =
                      ([rightExpression], .one) := by
                    apply Prod.ext
                    · exact hrightSingleton
                    · exact hrightShape
                  have hrightTarget : evalCrepRuntimeExp target rightExpression =
                      some rightWord := by
                    rw [hrightSingleton] at hrightRun
                    cases hvalue : evalCrepRuntimeExp target rightExpression with
                    | none => simp [evalCrepRuntimeExps, hvalue] at hrightRun
                    | some word =>
                        have heq : word = rightWord := by
                          simpa [evalCrepRuntimeExps, hvalue] using hrightRun
                        simp [heq]
                  have hleftRaw : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord left
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word leftWord) := by
                    simpa [evalPanSemStateExp] using hleftSource
                  have hrightRaw : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord right
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word rightWord) := by
                    simpa [evalPanSemStateExp] using hrightSource
                  have hcompare : (panSemBitVec64MemoryAccess source).compare
                      operator leftWord rightWord =
                      RiscV.panRiscVCmp operator leftWord rightWord := rfl
                  have hsourceComputed : evalPanValueExp source.structs
                      source.locals source.globals source.memory source.baseAddress
                      source.topAddress panSemBitVec64BytesInWord
                      (.cmp operator left right)
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word (RiscV.panRiscVCmp operator leftWord rightWord)) := by
                    simp [evalPanValueExp, hleftRaw, hrightRaw, hcompare]
                  have hsourceValue : result =
                      RiscV.panRiscVCmp operator leftWord rightWord := by
                    have hsourceCmp' : evalPanValueExp source.structs
                        source.locals source.globals source.memory source.baseAddress
                        source.topAddress panSemBitVec64BytesInWord
                        (.cmp operator left right)
                        (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                        some (.word result) := by
                      simpa [evalPanSemStateExp] using hsourceCmp
                    have hvalues : PanValue.word result =
                        PanValue.word (RiscV.panRiscVCmp operator leftWord rightWord) :=
                      Option.some.inj (hsourceCmp'.symm.trans hsourceComputed)
                    injection hvalues with hresult
                  have hcompiledCmp : compileExpHOL compilerContext
                      (.cmp operator left right) =
                      ([.cmp operator leftExpression rightExpression], .one) := by
                    simp [compileExpHOL, hleftPair, hrightPair]
                  subst result
                  have htargetCmp : evalCrepRuntimeExp target
                      (.cmp operator leftExpression rightExpression) =
                      some (RiscV.panRiscVCmp operator leftWord rightWord) := by
                    have hleftTarget' : evalCrepRuntimeExp
                        (riscvCrepWordTarget target) leftExpression = some leftWord := by
                      rw [hcanonical] at hleftTarget
                      exact hleftTarget
                    have hrightTarget' : evalCrepRuntimeExp
                        (riscvCrepWordTarget target) rightExpression = some rightWord := by
                      rw [hcanonical] at hrightTarget
                      exact hrightTarget
                    rw [hcanonical,
                      evalCrepRuntimeExp_cmp_riscvWordTarget_evalPanCmp]
                    rw [hleftTarget', hrightTarget']
                    exact congrArg some
                      (panRiscVCmp_eq_evalPanCmp operator leftWord rightWord).symm
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simp [compilerContext, hcompiledCmp, evalCrepRuntimeExps,
                      htargetCmp]
                  · simp [compilerContext, hcompiledCmp]
                  · simp [compilerContext, hcompiledCmp, panValueShape]
                  · simp [compilerContext, hcompiledCmp, isWfShape]
              | cons _ _ => simp [hrightCompiled] at hrightLength
      | cons _ _ => simp [hleftCompiled] at hleftLength

/-! The Shift constructor case for a full localized-expression IH, at the fixed
RISC-V target. This is induction support for the HOL expression relation; the
enclosing Call simulation remains open. -/
theorem compileExpHOL_shift_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : Shift) (left right : Exp (RiscV.Word 64))
    (leftWord rightWord result : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (hleftLocalized : expGlobalVars left = [])
    (hrightLocalized : expGlobalVars right = [])
    (hleftSource : evalPanSemStateExp source left = some (.word leftWord))
    (hrightSource : evalPanSemStateExp source right = some (.word rightWord))
    (hleftIH : ∀ value,
      evalPanSemStateExp source left = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars left = [] →
      evalCrepRuntimeExps target (compileExpHOL
        (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
        left).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) left).1.length =
            Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
              context.funcs context.vmax context.eids) left).2 ∧
        panValueShape [] value = (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) left).2 ∧
        isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) left).2 = true)
    (hrightIH : ∀ value,
      evalPanSemStateExp source right = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars right = [] →
      evalCrepRuntimeExps target (compileExpHOL
        (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
        right).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) right).1.length =
            Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
              context.funcs context.vmax context.eids) right).2 ∧
        panValueShape [] value = (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) right).2 ∧
        isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
          context.funcs context.vmax context.eids) right).2 = true)
    (hsourceShift : evalPanSemStateExp source (.shift operator left right) =
      some (.word result)) :
    evalCrepRuntimeExps target (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.shift operator left right)).1 = some [result] ∧
    (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs context.vmax
      context.eids)
      (.shift operator left right)).1.length = Shape.shapeSize
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs context.vmax
          context.eids)
          (.shift operator left right)).2 ∧
    panValueShape [] (.word result) = (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.shift operator left right)).2 ∧
    isWfShape [] (compileExpHOL
      (panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids)
      (.shift operator left right)).2 = true := by
  let compilerContext :=
    panToCrepMkCtxtHOL context.vars context.funcs context.vmax context.eids
  have hleftRel := hleftIH (.word leftWord) hleftSource hstate hcode hlocals
    hleftLocalized
  have hrightRel := hrightIH (.word rightWord) hrightSource hstate hcode hlocals
    hrightLocalized
  have hleftShape : (compileExpHOL compilerContext left).2 = .one := by
    have h := hleftRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have hrightShape : (compileExpHOL compilerContext right).2 = .one := by
    have h := hrightRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have hleftRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext left).1 = some [leftWord] := by
    simpa [compilerContext, panValueFlatten] using hleftRel.1
  have hrightRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext right).1 = some [rightWord] := by
    simpa [compilerContext, panValueFlatten] using hrightRel.1
  have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
    have h := hleftRel.2.1
    rw [hleftShape] at h
    simpa using h
  have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
    have h := hrightRel.2.1
    rw [hrightShape] at h
    simpa using h
  cases hleftCompiled : (compileExpHOL compilerContext left).1 with
  | nil => simp [hleftCompiled] at hleftLength
  | cons leftExpression leftTail =>
      cases leftTail with
      | nil =>
          have hleftSingleton : (compileExpHOL compilerContext left).1 =
              [leftExpression] := by simp [hleftCompiled]
          have hleftPair : compileExpHOL compilerContext left =
              ([leftExpression], .one) := by
            apply Prod.ext
            · exact hleftSingleton
            · exact hleftShape
          have hleftTarget : evalCrepRuntimeExp target leftExpression =
              some leftWord := by
            rw [hleftSingleton] at hleftRun
            cases hvalue : evalCrepRuntimeExp target leftExpression with
            | none => simp [evalCrepRuntimeExps, hvalue] at hleftRun
            | some word =>
                have heq : word = leftWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hleftRun
                simp [heq]
          cases hrightCompiled : (compileExpHOL compilerContext right).1 with
          | nil => simp [hrightCompiled] at hrightLength
          | cons rightExpression rightTail =>
              cases rightTail with
              | nil =>
                  have hrightSingleton : (compileExpHOL compilerContext right).1 =
                      [rightExpression] := by simp [hrightCompiled]
                  have hrightPair : compileExpHOL compilerContext right =
                      ([rightExpression], .one) := by
                    apply Prod.ext
                    · exact hrightSingleton
                    · exact hrightShape
                  have hrightTarget : evalCrepRuntimeExp target rightExpression =
                      some rightWord := by
                    rw [hrightSingleton] at hrightRun
                    cases hvalue : evalCrepRuntimeExp target rightExpression with
                    | none => simp [evalCrepRuntimeExps, hvalue] at hrightRun
                    | some word =>
                        have heq : word = rightWord := by
                          simpa [evalCrepRuntimeExps, hvalue] using hrightRun
                        simp [heq]
                  have hleftRaw : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord left
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word leftWord) := by
                    simpa [evalPanSemStateExp] using hleftSource
                  have hrightRaw : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord right
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word rightWord) := by
                    simpa [evalPanSemStateExp] using hrightSource
                  have hshift : (panSemBitVec64MemoryAccess source).shift
                      operator leftWord rightWord =
                      RiscV.panRiscVShift operator leftWord rightWord := rfl
                  have hsourceComputed : evalPanValueExp source.structs
                      source.locals source.globals source.memory source.baseAddress
                      source.topAddress panSemBitVec64BytesInWord
                      (.shift operator left right)
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      (RiscV.panRiscVShift operator leftWord rightWord).map PanValue.word := by
                    simp [evalPanValueExp, hleftRaw, hrightRaw, hshift]
                  have hsourceShift' : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord (.shift operator left right)
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word result) := by
                    simpa [evalPanSemStateExp] using hsourceShift
                  have hshiftResult : RiscV.panRiscVShift operator leftWord rightWord =
                      some result := by
                    cases hcomputed : RiscV.panRiscVShift operator leftWord rightWord with
                    | none =>
                        have hvalues := hsourceShift'.symm.trans hsourceComputed
                        simp [hcomputed] at hvalues
                    | some word =>
                        have heq : PanValue.word result = PanValue.word word := by
                          apply Option.some.inj
                          simpa [hcomputed] using hsourceShift'.symm.trans hsourceComputed
                        have hresult : result = word := by
                          injection heq
                        subst result
                        rfl
                  have hcompiledShift : compileExpHOL compilerContext
                      (.shift operator left right) =
                      ([.shift operator leftExpression rightExpression], .one) := by
                    simp [compileExpHOL, hleftPair, hrightPair]
                  have htargetShift : evalCrepRuntimeExp target
                      (.shift operator leftExpression rightExpression) = some result := by
                    have hleftTarget' : evalCrepRuntimeExp
                        (riscvCrepWordTarget target) leftExpression = some leftWord := by
                      rw [hcanonical] at hleftTarget
                      exact hleftTarget
                    have hrightTarget' : evalCrepRuntimeExp
                        (riscvCrepWordTarget target) rightExpression = some rightWord := by
                      rw [hcanonical] at hrightTarget
                      exact hrightTarget
                    rw [hcanonical,
                      evalCrepRuntimeExp_shift_riscvWordTarget_evalPanShift]
                    rw [hleftTarget', hrightTarget']
                    simp only [Option.bind_some]
                    calc
                      evalPanShiftFull operator leftWord rightWord =
                          RiscV.panRiscVShift operator leftWord rightWord :=
                        (panRiscVShift_eq_evalPanShiftFull operator leftWord rightWord).symm
                      _ = some result := hshiftResult
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simp [compilerContext, hcompiledShift, evalCrepRuntimeExps,
                      htargetShift]
                  · simp [compilerContext, hcompiledShift]
                  · simp [compilerContext, hcompiledShift, panValueShape]
                  · simp [compilerContext, hcompiledShift, isWfShape]
              | cons _ _ => simp [hrightCompiled] at hrightLength
      | cons _ _ => simp [hleftCompiled] at hleftLength

/-! Full-IH constructor evidence includes Cmp, Shift, and the LoadByte/Load32
address cases below. The separate restricted argument support composes
Const/Local/RStruct/address/RField cases and PanOp multiplication through HOL
`compile_args`. The general compile_exp_val_rel induction, remaining Load forms
and operators, and the enclosing Call proof remain open. -/
private theorem evalPanSemStateExp_panOpMul_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (left right : Exp (RiscV.Word 64)) (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.panOp .mul [left, right]) =
      some (.word result)) :
    ∃ leftWord rightWord,
      evalPanSemStateExp source left = some (.word leftWord) ∧
      evalPanSemStateExp source right = some (.word rightWord) ∧
      result = leftWord * rightWord := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.panOp .mul [left, right])
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  cases hleft : evalPanSemStateExp source left with
  | none =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
        simpa [evalPanSemStateExp] using hleft
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleftValue,
        evalPanOp] at hsourceValue
  | some leftValue =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
          some leftValue := by
        simpa [evalPanSemStateExp] using hleft
      cases hright : evalPanSemStateExp source right with
      | none =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hright
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue, hrightValue, evalPanOp] at hsourceValue
      | some rightValue =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
              some rightValue := by
            simpa [evalPanSemStateExp] using hright
          cases leftValue with
          | word leftWord =>
              cases rightValue with
              | word rightWord =>
                  have hcomputed : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord (.panOp .mul [left, right])
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word (leftWord * rightWord)) := by
                    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftValue, hrightValue, evalPanOp]
                  have hwords : PanValue.word result =
                      PanValue.word (leftWord * rightWord) :=
                    Option.some.inj (hsourceValue.symm.trans hcomputed)
                  exact ⟨leftWord, rightWord, rfl, rfl,
                    PanValue.word.inj hwords⟩
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue, evalPanOp] at hsourceValue
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue, evalPanOp] at hsourceValue
          | rStruct _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue, evalPanOp] at hsourceValue
          | nStruct _ _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue, evalPanOp] at hsourceValue

private theorem panValues_eq_words_map_of_wordProjection
    (values : List (PanValue (RiscV.Word 64)))
    (words : List (RiscV.Word 64))
    (hvalues : values.mapM panValueWordProjection = some words) :
    values = words.map PanValue.word := by
  induction values generalizing words with
  | nil => simpa using hvalues.symm
  | cons value values ih =>
      cases value with
      | word word =>
          cases htail : values.mapM panValueWordProjection with
          | none => simp [List.mapM_cons, panValueWordProjection, htail] at hvalues
          | some tail =>
              have hwords : words = word :: tail := by
                simpa [List.mapM_cons, htail] using hvalues.symm
              subst words
              have htailValues : values = tail.map PanValue.word := ih tail htail
              simp [htailValues]
      | rStruct fields => simp [List.mapM_cons, panValueWordProjection] at hvalues
      | nStruct name fields => simp [List.mapM_cons, panValueWordProjection] at hvalues

private theorem evalPanSemStateExp_op_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.op operator arguments) =
      some (.word result)) :
    ∃ words,
      evalPanSemStateExps source arguments = some (words.map PanValue.word) ∧
      wordOpHOL operator words = some result := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.op operator arguments)
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  simp only [evalPanValueExp] at hsourceValue
  cases harguments : evalPanSemStateExps source arguments with
  | none =>
      change evalPanValueExp.evalPanValueExps source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord arguments (some (panSemBitVec64MemoryAccess source)) =
        none at harguments
      rw [harguments] at hsourceValue
      simp at hsourceValue
  | some values =>
      change evalPanValueExp.evalPanValueExps source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord arguments (some (panSemBitVec64MemoryAccess source)) =
        some values at harguments
      rw [harguments] at hsourceValue
      cases hprojection : values.mapM panValueWordProjection with
      | none => simp [hprojection] at hsourceValue
      | some words =>
          have hvalues : values = words.map PanValue.word :=
            panValues_eq_words_map_of_wordProjection values words hprojection
          have hwordMap : (words.map PanValue.word).mapM panValueWordProjection =
              some words := by
            simp only [List.mapM_map]
            change words.mapM (fun word => some word) = some words
            simpa using (List.mapM_pure (m := Option) (f := id) (l := words))
          have hwordOp : (panSemBitVec64MemoryAccess source).wordOp
              operator words = wordOpHOL operator words := rfl
          simp [hvalues, hwordMap, hwordOp] at hsourceValue
          have hresultEq : wordOpHOL operator words = some result := by
            cases hword : wordOpHOL operator words with
            | none => simp [hword] at hsourceValue
            | some word =>
                have heq : word = result := by
                  have hwordValues : PanValue.word word = PanValue.word result := by
                    simpa [hword] using hsourceValue
                  exact PanValue.word.inj hwordValues
                simp [heq]
          exact ⟨words, congrArg some hvalues, hresultEq⟩

private theorem evalPanSemStateExp_op2_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (operator : BinOp) (left right : Exp (RiscV.Word 64))
    (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.op operator [left, right]) =
      some (.word result)) :
    ∃ leftWord rightWord,
      evalPanSemStateExp source left = some (.word leftWord) ∧
      evalPanSemStateExp source right = some (.word rightWord) ∧
      wordOpHOL operator [leftWord, rightWord] = some result := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.op operator [left, right])
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  cases hleft : evalPanSemStateExp source left with
  | none =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
        simpa [evalPanSemStateExp] using hleft
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleftValue] at hsourceValue
  | some leftValue =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
          some leftValue := by
        simpa [evalPanSemStateExp] using hleft
      cases hright : evalPanSemStateExp source right with
      | none =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hright
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue, hrightValue] at hsourceValue
      | some rightValue =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
              some rightValue := by
            simpa [evalPanSemStateExp] using hright
          cases leftValue with
          | word leftWord =>
              cases rightValue with
              | word rightWord =>
                  have hwordOp : (panSemBitVec64MemoryAccess source).wordOp
                      operator [leftWord, rightWord] =
                      wordOpHOL operator [leftWord, rightWord] := by
                    rfl
                  have hcomputed : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord (.op operator [left, right])
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      (wordOpHOL operator [leftWord, rightWord]).map PanValue.word := by
                    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftValue, hrightValue, hwordOp]
                  rw [hcomputed] at hsourceValue
                  cases hword : wordOpHOL operator [leftWord, rightWord] with
                  | none => simp [hword] at hsourceValue
                  | some word =>
                      have hresultEq : result = word := by
                        have hvalues : PanValue.word result = PanValue.word word := by
                          simpa [hword] using hsourceValue.symm
                        exact PanValue.word.inj hvalues
                      subst result
                      exact ⟨leftWord, rightWord, by rfl,
                        by rfl, hword⟩
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue] at hsourceValue
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue] at hsourceValue
          | rStruct _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue] at hsourceValue
          | nStruct _ _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue] at hsourceValue

/-! Binary `Op` argument support for HOL `compile_exp_val_rel`. The source
evaluator forces both operands to words and computes with HOL `word_op`; the
full operand IHs then give singleton production Crep operands. This handles
the two-argument slice only; general arity and the enclosing Call proof remain
open. -/
theorem compileExpHOL_op2_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : BinOp) (left right : Exp (RiscV.Word 64))
    (result : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (hleftLocalized : expGlobalVars left = [])
    (hrightLocalized : expGlobalVars right = [])
    (hsource : evalPanSemStateExp source (.op operator [left, right]) =
      some (.word result))
    (hleftIH : ∀ value,
      evalPanSemStateExp source left = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars left = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            left).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).1.length = Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            left).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).2 = true)
    (hrightIH : ∀ value,
      evalPanSemStateExp source right = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars right = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            right).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).1.length = Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            right).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).2 = true) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.op operator [left, right])).1 = some [result] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator [left, right])).1.length = Shape.shapeSize
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.op operator [left, right])).2 ∧
      panValueShape [] (.word result) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator [left, right])).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator [left, right])).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  obtain ⟨leftWord, rightWord, hleft, hright, hresult⟩ :=
    evalPanSemStateExp_op2_inv source operator left right result hsource
  have hleftRel := hleftIH (.word leftWord) hleft hstate hcode hlocals hleftLocalized
  have hrightRel := hrightIH (.word rightWord) hright hstate hcode hlocals hrightLocalized
  have hleftShape : (compileExpHOL compilerContext left).2 = .one := by
    simpa [compilerContext, panValueShape] using hleftRel.2.2.1.symm
  have hrightShape : (compileExpHOL compilerContext right).2 = .one := by
    simpa [compilerContext, panValueShape] using hrightRel.2.2.1.symm
  have hleftRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext left).1 = some [leftWord] := by
    simpa [compilerContext, panValueFlatten] using hleftRel.1
  have hrightRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext right).1 = some [rightWord] := by
    simpa [compilerContext, panValueFlatten] using hrightRel.1
  have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
    exact (evalCrepRuntimeExps_length_of_some target
      (compileExpHOL compilerContext left).1 [leftWord] hleftRun).symm
  have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
    exact (evalCrepRuntimeExps_length_of_some target
      (compileExpHOL compilerContext right).1 [rightWord] hrightRun).symm
  cases hleftCompiled : (compileExpHOL compilerContext left).1 with
  | nil => simp [hleftCompiled] at hleftLength
  | cons leftExpression leftTail =>
      cases leftTail with
      | nil =>
          have hleftSingleton : (compileExpHOL compilerContext left).1 =
              [leftExpression] := by simp [hleftCompiled]
          have hleftExpressionRun : evalCrepRuntimeExp target leftExpression =
              some leftWord := by
            rw [hleftSingleton] at hleftRun
            cases hword : evalCrepRuntimeExp target leftExpression with
            | none => simp [evalCrepRuntimeExps, hword] at hleftRun
            | some word =>
                have hwordEq : word = leftWord := by
                  simpa [evalCrepRuntimeExps, hword] using hleftRun
                simp [hwordEq]
          cases hrightCompiled : (compileExpHOL compilerContext right).1 with
          | nil => simp [hrightCompiled] at hrightLength
          | cons rightExpression rightTail =>
              cases rightTail with
              | nil =>
                  have hrightSingleton : (compileExpHOL compilerContext right).1 =
                      [rightExpression] := by simp [hrightCompiled]
                  have hrightExpressionRun : evalCrepRuntimeExp target rightExpression =
                      some rightWord := by
                    rw [hrightSingleton] at hrightRun
                    cases hword : evalCrepRuntimeExp target rightExpression with
                    | none => simp [evalCrepRuntimeExps, hword] at hrightRun
                    | some word =>
                        have hwordEq : word = rightWord := by
                          simpa [evalCrepRuntimeExps, hword] using hrightRun
                        simp [hwordEq]
                  have hcompiled : compileExpHOL compilerContext
                      (.op operator [left, right]) =
                      ([.op operator [leftExpression, rightExpression]], .one) := by
                    simp [compileExpHOL, compileExpHOL.compileExpListHOL,
                      hleftSingleton, hrightSingleton, cexpHeads]
                  have hleftExpressionRunCanonical :
                      evalCrepRuntimeExp (riscvCrepWordTarget target) leftExpression =
                        some leftWord := by
                    rw [hcanonical] at hleftExpressionRun
                    exact hleftExpressionRun
                  have hrightExpressionRunCanonical :
                      evalCrepRuntimeExp (riscvCrepWordTarget target) rightExpression =
                        some rightWord := by
                    rw [hcanonical] at hrightExpressionRun
                    exact hrightExpressionRun
                  have htargetOp : evalCrepRuntimeExp target
                      (.op operator [leftExpression, rightExpression]) = some result := by
                    rw [hcanonical, evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
                    simpa [List.mapM_cons, hleftExpressionRunCanonical,
                      hrightExpressionRunCanonical] using hresult
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simp [compilerContext, hcompiled, evalCrepRuntimeExps, htargetOp]
                  · simp [compilerContext, hcompiled]
                  · simp [compilerContext, hcompiled, panValueShape]
                  · simp [compilerContext, hcompiled, isWfShape]
              | cons _ _ => simp [hrightCompiled] at hrightLength
      | cons _ _ => simp [hleftCompiled] at hleftLength

/-! Arbitrary-arity `Op` constructor support for HOL `compile_exp_val_rel`.
Successful source evaluation supplies word-valued operands and the exact HOL
`word_op` result; each operand's full IH lifts the compiled argument list to
the production RISC-V target evaluator. This is an induction step, not the
complete expression relation or enclosing Call theorem. -/
theorem compileExpHOL_op_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (result : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hcanonical : target = riscvCrepWordTarget target)
    (hlocalized : ∀ expression, expression ∈ arguments →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExp source (.op operator arguments) =
      some (.word result))
    (hargumentsIH : ∀ expression, expression ∈ arguments → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length = Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.op operator arguments)).1 = some [result] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator arguments)).1.length = Shape.shapeSize
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.op operator arguments)).2 ∧
      panValueShape [] (.word result) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator arguments)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.op operator arguments)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  obtain ⟨words, hsourceArguments, hwordOp⟩ :=
    evalPanSemStateExp_op_inv source operator arguments result hsource
  have hargumentsShape : ∀ expression, expression ∈ arguments →
      (compileExpHOL compilerContext expression).2 = .one := by
    intro expression hmem
    obtain ⟨word, heval⟩ := evalPanSemStateExps_member_word
      source arguments words hsourceArguments hmem
    have hfull := hargumentsIH expression hmem (.word word) heval
      hstate hcode hlocals (hlocalized expression hmem)
    simpa [compilerContext, panValueShape] using hfull.2.2.1.symm
  have hargumentsLength : ∀ expression, expression ∈ arguments →
      (compileExpHOL compilerContext expression).1.length = 1 := by
    intro expression hmem
    obtain ⟨word, heval⟩ := evalPanSemStateExps_member_word
      source arguments words hsourceArguments hmem
    have hfull := hargumentsIH expression hmem (.word word) heval
      hstate hcode hlocals (hlocalized expression hmem)
    simpa [compilerContext, hargumentsShape expression hmem] using hfull.2.1
  have hcompiledHeads := compileExpListHOL_heads_eq_compileArgs_of_singleton
    compilerContext arguments hargumentsShape hargumentsLength
  have heach : ∀ expression, expression ∈ arguments → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    have hfull := hargumentsIH expression hmem value heval
      hstate hcode hlocals (hlocalized expression hmem)
    exact hfull.1
  have hcompiledArguments := compileArgsHOL_eval_flatten_of_each
    compilerContext source target arguments (words.map PanValue.word)
    hsourceArguments heach
  have hargumentsRun : evalCrepRuntimeExps target
      (compileArgsHOL compilerContext arguments) = some words := by
    simpa [panValueFlatten_wordList] using hcompiledArguments
  have hargumentsRunCanonical : evalCrepRuntimeExps
      (riscvCrepWordTarget target) (compileArgsHOL compilerContext arguments) =
        some words := by
    rw [← hcanonical]
    exact hargumentsRun
  have hargumentsMap : (compileArgsHOL compilerContext arguments).mapM
      (evalCrepRuntimeExp (riscvCrepWordTarget target)) = some words := by
    rw [← evalCrepRuntimeExps_eq_mapM]
    exact hargumentsRunCanonical
  have htargetOp : evalCrepRuntimeExp target
      (.op operator (compileArgsHOL compilerContext arguments)) = some result := by
    rw [hcanonical, evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL,
      hargumentsMap]
    exact hwordOp
  have hcompiled : compileExpHOL compilerContext (.op operator arguments) =
      ([.op operator (compileArgsHOL compilerContext arguments)], .one) := by
    have hcompiledHeads' : cexpHeads
        (arguments.map fun expression => (compileExpHOL compilerContext expression).1) =
        some (compileArgsHOL compilerContext arguments) := by
      simpa only [List.map_map, Function.comp_def] using hcompiledHeads
    simp only [compileExpHOL]
    rw [compileExpListHOL_map_fst_eq_map_compileExp, hcompiledHeads']
  have htargetRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext (.op operator arguments)).1 = some [result] := by
    rw [hcompiled]
    simp [evalCrepRuntimeExps, htargetOp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [compilerContext, panValueFlatten] using htargetRun
  · simp [compilerContext, hcompiled]
  · simp [compilerContext, hcompiled, panValueShape]
  · simp [compilerContext, hcompiled, isWfShape]

/-! The supported PanOp Mul constructor case for the full localized expression
relation. The successful source evaluator forces exactly two word operands;
their full IHs determine singleton compiled target operands, after which the
production Crep Mul node computes the same word. -/
theorem compileExpHOL_panOpMul_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (left right : Exp (RiscV.Word 64))
    (result : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hleftLocalized : expGlobalVars left = [])
    (hrightLocalized : expGlobalVars right = [])
    (hsource : evalPanSemStateExp source (.panOp .mul [left, right]) =
      some (.word result))
    (hleftIH : ∀ value,
      evalPanSemStateExp source left = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars left = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            left).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).1.length = Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            left).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          left).2 = true)
    (hrightIH : ∀ value,
      evalPanSemStateExp source right = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars right = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            right).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).1.length = Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            right).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          right).2 = true) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.panOp .mul [left, right])).1 =
        some (panValueFlatten (.word result)) ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.panOp .mul [left, right])).1.length = Shape.shapeSize
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.panOp .mul [left, right])).2 ∧
      panValueShape [] (.word result) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.panOp .mul [left, right])).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.panOp .mul [left, right])).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  obtain ⟨leftWord, rightWord, hleft, hright, hresult⟩ :=
    evalPanSemStateExp_panOpMul_inv source left right result hsource
  have hleftRel := hleftIH (.word leftWord) hleft hstate hcode hlocals hleftLocalized
  have hrightRel := hrightIH (.word rightWord) hright hstate hcode hlocals hrightLocalized
  have hleftShape : (compileExpHOL compilerContext left).2 = .one := by
    simpa [compilerContext, panValueShape] using hleftRel.2.2.1.symm
  have hrightShape : (compileExpHOL compilerContext right).2 = .one := by
    simpa [compilerContext, panValueShape] using hrightRel.2.2.1.symm
  have hleftRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext left).1 = some [leftWord] := by
    simpa [compilerContext, panValueFlatten] using hleftRel.1
  have hrightRun : evalCrepRuntimeExps target
      (compileExpHOL compilerContext right).1 = some [rightWord] := by
    simpa [compilerContext, panValueFlatten] using hrightRel.1
  have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
    simpa using (evalCrepRuntimeExps_length_of_some target
      (compileExpHOL compilerContext left).1 [leftWord] hleftRun).symm
  have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
    simpa using (evalCrepRuntimeExps_length_of_some target
      (compileExpHOL compilerContext right).1 [rightWord] hrightRun).symm
  cases hleftCompiled : (compileExpHOL compilerContext left).1 with
  | nil => simp [hleftCompiled] at hleftLength
  | cons leftExpression leftTail =>
      cases leftTail with
      | nil =>
          have hleftSingleton : (compileExpHOL compilerContext left).1 =
              [leftExpression] := by simp [hleftCompiled]
          have hleftExpressionRun :
              evalCrepRuntimeExp target leftExpression = some leftWord := by
            rw [hleftSingleton] at hleftRun
            cases hword : evalCrepRuntimeExp target leftExpression with
            | none => simp [evalCrepRuntimeExps, hword] at hleftRun
            | some word =>
                have hwordEq : word = leftWord := by
                  simpa [evalCrepRuntimeExps, hword] using hleftRun
                simp [hwordEq]
          cases hrightCompiled : (compileExpHOL compilerContext right).1 with
          | nil => simp [hrightCompiled] at hrightLength
          | cons rightExpression rightTail =>
              cases rightTail with
              | nil =>
                  have hrightSingleton : (compileExpHOL compilerContext right).1 =
                      [rightExpression] := by simp [hrightCompiled]
                  have hrightExpressionRun :
                      evalCrepRuntimeExp target rightExpression = some rightWord := by
                    rw [hrightSingleton] at hrightRun
                    cases hword : evalCrepRuntimeExp target rightExpression with
                    | none => simp [evalCrepRuntimeExps, hword] at hrightRun
                    | some word =>
                        have hwordEq : word = rightWord := by
                          simpa [evalCrepRuntimeExps, hword] using hrightRun
                        simp [hwordEq]
                  have hcompiled : compileExpHOL compilerContext
                      (.panOp .mul [left, right]) =
                      ([.crepOp .mul [leftExpression, rightExpression]], .one) := by
                    simp [compileExpHOL, compileExpHOL.compileExpListHOL,
                      hleftSingleton, hrightSingleton, cexpHeads, compilePanOp]
                  have htargetMul : evalCrepRuntimeExps target
                      (compileExpHOL compilerContext (.panOp .mul [left, right])).1 =
                      some [leftWord * rightWord] := by
                    rw [hcompiled]
                    simp [evalCrepRuntimeExps, evalCrepRuntimeExp,
                      crepOpCrep, hleftExpressionRun, hrightExpressionRun]
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · simpa [compilerContext, hresult, panValueFlatten] using htargetMul
                  · simp [compilerContext, hcompiled]
                  · simp [compilerContext, hcompiled, panValueShape]
                  · simp [compilerContext, hcompiled, isWfShape]
              | cons _ _ => simp [hrightCompiled] at hrightLength
      | cons _ _ => simp [hleftCompiled] at hleftLength

theorem compileArgsHOL_constLocalStructAddressOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression)
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
    exact compileArgConstLocalStructAddressOrRFieldInnerIH_eval_flatten
      context source target (hsupported expression hmem) hstate hcode hlocals
      value heval
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

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
      compileArgConstLocalStructAddress source expression)
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
    exact compileExpHOL_constLocalStructAddress_eval_flatten context source target
      expression value hstate hlocals (hsupported expression hmem) heval
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

/-! A successful source parameter-shape match preserves `Shape.shapeSize`.
Named shapes also satisfy this because every named shape has size one; their
name equality is only the matching condition. -/
mutual
  private theorem panShapeMatches_shapeSize_eq (left right : Shape)
      (hmatch : panShapeMatches left right = true) :
      Shape.shapeSize left = Shape.shapeSize right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches] at hmatch ⊢
    | named leftName =>
        cases right <;> simp [panShapeMatches] at hmatch ⊢
    | comb leftFields =>
        cases right with
        | one => simp [panShapeMatches] at hmatch
        | named _ => simp [panShapeMatches] at hmatch
        | comb rightFields =>
            simp only [panShapeMatches] at hmatch
            rw [shapeSize_comb_eq_sum, shapeSize_comb_eq_sum]
            exact panShapeListMatches_shapeSize_eq leftFields rightFields hmatch

  private theorem panShapeListMatches_shapeSize_eq (left right : List Shape)
      (hmatch : panShapeMatches.panShapeListMatches left right = true) :
      (left.map Shape.shapeSize).sum = (right.map Shape.shapeSize).sum := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches] at hmatch ⊢
    | cons leftHead leftTail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches] at hmatch
        | cons rightHead rightTail =>
            simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true] at hmatch
            rcases hmatch with ⟨hhead, htail⟩
            simp only [List.map_cons, List.sum_cons]
            rw [panShapeMatches_shapeSize_eq leftHead rightHead hhead,
              panShapeListMatches_shapeSize_eq leftTail rightTail htail]
end

/-! The successful `lookup_code` parameter check fixes each formal shape to its
source `shape_of` argument shape. This Flapjack projection exposes the
map-level fact needed by the indexed HOL `LIST_REL` locals bridge. -/
private theorem panSemCodeArgumentsMatch_shapeMapEq (structs : StructContext)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (hmatch : panSemCodeArgumentsMatch structs parameters values = true) :
    parameters.map Prod.snd = values.map (panValueShape structs) := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          rcases hmatch with ⟨hshape, htail⟩
          simp only [List.map_cons]
          rw [panShapeMatches_eq (panValueShape structs value) parameter.2 hshape,
            ih values htail]

private theorem panSemCodeArgumentsMatch_length (structs : StructContext)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (hmatch : panSemCodeArgumentsMatch structs parameters values = true) :
    parameters.length = values.length := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          exact congrArg Nat.succ (ih values hmatch.2)

/-! Successful source parameter matching plus well-formed source values fixes
the flattened argument length used by target code lookup. -/
private theorem panSemCodeArgumentsMatch_flattenLength
    (parameters : List (String × Shape)) (values : List (PanValue (RiscV.Word 64)))
    (hmatch : panSemCodeArgumentsMatch [] parameters values = true)
    (hwf : panValueIsWfValues ([] : StructContext) values = true) :
    Shape.shapeSize (.comb (parameters.map Prod.snd)) =
      (values.flatMap panValueFlatten).length := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch, Shape.shapeSize] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          rcases hmatch with ⟨hshape, htailMatch⟩
          simp only [panValueIsWfValues, Bool.and_eq_true] at hwf
          have hshapeSize := panShapeMatches_shapeSize_eq
            (panValueShape [] value) parameter.2 hshape
          have hwfShape : isWfShape [] (panValueShape [] value) = true :=
            panValueIsWf_isWfShape_panValueShape [] value hwf.1
          have hflatLength := panValueFlatten_length_eq_shapeSize value hwfShape
          have htail := ih values htailMatch hwf.2
          calc
            Shape.shapeSize (.comb ((parameter :: parameters).map Prod.snd)) =
                Shape.shapeSize parameter.2 +
                  Shape.shapeSize (.comb (parameters.map Prod.snd)) := by
              simp only [shapeSize_comb_eq_sum, List.map_cons, List.sum_cons]
            _ = (panValueFlatten value).length +
                  (values.flatMap panValueFlatten).length := by
              rw [← hshapeSize, ← hflatLength, htail]
            _ = ((value :: values).flatMap panValueFlatten).length := by
              simp [List.flatMap, List.length_append]

private theorem panSemCodeArgumentsMatch_of_lookup_success [BEq String]
    (structs : StructContext) (code : PanSemCodeMap α) (function : String)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (body : Prog α) (returnShape : Shape)
    (locals : String → Option (PanValue α))
    (hentry : panSemCodeLookup code function = some (parameters, body, returnShape))
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, locals)) :
    panSemCodeArgumentsMatch structs parameters values = true := by
  cases hargs : panSemCodeArgumentsMatch structs parameters values with
  | true => rfl
  | false => simp [lookupPanSemCodeCall, hentry, hargs] at hlookup

/-! Successful state-owned `lookupPanSemCodeCall` exposes the same parameter
map returned by the source evaluator's callee-entry setup. This projection
connects its body lookup to the binder-to-`slc` locals relation in PanToCrep. -/
private theorem bindPanValueParameters_of_lookup_success [BEq String]
    (structs : StructContext) (code : PanSemCodeMap α) (function : String)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (body : Prog α) (returnShape : Shape)
    (locals : String → Option (PanValue α))
    (hentry : panSemCodeLookup code function = some (parameters, body, returnShape))
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, locals)) :
    (parameters.map Prod.fst).Nodup ∧
      bindPanValueParameters (parameters.map Prod.fst) values = some locals := by
  have hmatch := panSemCodeArgumentsMatch_of_lookup_success structs code function
    parameters values body returnShape locals hentry hlookup
  have hnames : (parameters.map Prod.fst).Nodup := by
    by_cases hnames : (parameters.map Prod.fst).Nodup
    · exact hnames
    · simp [lookupPanSemCodeCall, hentry, hnames] at hlookup
  have hbind : bindPanValueParameters (parameters.map Prod.fst) values = some locals := by
    have hlookup' := hlookup
    simp [lookupPanSemCodeCall, hentry, hnames, hmatch] at hlookup'
    cases hbind : bindPanValueParameters (parameters.map Prod.fst) values with
    | none => simp [hbind] at hlookup'
    | some bound =>
        simp [hbind] at hlookup'
        cases hlookup'
        rfl
  exact ⟨hnames, hbind⟩

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

private theorem crepRuntimeLocals_zip_eq_fupdateList
    (slots : List Nat) (words : List (RiscV.Word 64))
    (locals : Nat → Option (PanWordLab (RiscV.Word 64))) :
    (slots.zip words).foldl
        (fun locals (slot, word) => updateCrepRuntimeLocal locals slot (.word word))
        locals =
      FUPDATE_LIST locals (slots.zip (words.map PanWordLab.word)) := by
  induction slots generalizing words locals with
  | nil => cases words <;> simp [FUPDATE_LIST]
  | cons slot slots ih =>
      cases words with
      | nil => rfl
      | cons word words =>
          simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons, FUPDATE_LIST]
          have hfirst : updateCrepRuntimeLocal locals slot (.word word) =
              FUPDATE locals (slot, .word word) := by
            funext key
            by_cases hkey : key = slot
            · subst key
              simp [updateCrepRuntimeLocal, FUPDATE]
            · have hslotKey : (slot == key) = false := by
                exact beq_eq_false_iff_ne.mpr (Ne.symm hkey)
              simp [updateCrepRuntimeLocal, FUPDATE, hslotKey]
          rw [hfirst, ih]
          rfl

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
  have hnamesNodup : names.Nodup := by simp [names, List.nodup_range]
  refine ⟨(names.zip argumentWords).foldl
      (fun locals (name, value) =>
        updateCrepRuntimeLocal locals name (.word value))
      (fun _ => none : Nat → Option (PanWordLab (RiscV.Word 64))), ?_, rfl⟩
  simp only [lookupCrepRuntimeCode, lookupCrepHolCode, htargetEntry]
  have hvalid : names.length = (argumentWords.map PanWordLab.word).length ∧ names.Nodup := by
    simp [names, hnamesLength, hnamesNodup]
  rw [if_pos hvalid]
  apply congrArg some
  apply Prod.ext
  · rfl
  ·
    change FUPDATE_LIST (fun _ : Nat => none)
        (names.zip (argumentWords.map PanWordLab.word)) = _
    exact (crepRuntimeLocals_zip_eq_fupdateList names argumentWords
      (fun _ => none)).symm

/-! Relate arbitrary-list target `exp_hdl` writes to the source handler-local
assignment. This supplies the handler-body `locals_rel` premise for any
flattened payload whose words are present in the target return-global area;
the full state/code/excp relation and enclosing Call IH composition remain
separate Flapjack-only obligations. -/
theorem crepRuntimeExpHdlFiniteMapWords_localsRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (sourceLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (name : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (values : List (RiscV.Word 64))
    (hlocals : localsRel context sourceLocals state.locals)
    (hsource : FLOOKUP sourceLocals name = some old)
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars name = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current, state.locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel state 0 slots values) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2) state
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      localsRel context (FUPDATE sourceLocals (name, payload)) targetPost.locals := by
  obtain ⟨payloadSlots, hcontextPayload, _hslotsDistinct, hlocalsPayload⟩ :=
    localsRelUpdateExistingValue context sourceLocals state.locals name old payload
      hlocals hsource hshape
  have hpayloadSlots : payloadSlots = slots := by
    have hcontextTarget : FLOOKUP context.vars name =
        some (panValueShape [] payload, slots) := by
      rw [hpayloadShape]
      exact hvariable
    have hpairs : (panValueShape [] payload, payloadSlots) =
        (panValueShape [] payload, slots) := by
      exact Option.some.inj (hcontextPayload.symm.trans hcontextTarget)
    exact congrArg Prod.snd hpairs
  let targetPost := { state with locals :=
    ((slots.zip values).foldl
      (fun locals (entry : Nat × RiscV.Word 64) =>
        updateCrepRuntimeLocal locals entry.1 (.word entry.2))
      state.locals) }
  have hrun := crepRuntimeExpHdlFiniteMapWords handler primitive state context.vars
    name shape slots values hvariable hslots hglobals
  have hrunPost : evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (expHdlFiniteMap context.vars name) = some (.normal, targetPost) := by
    simpa [targetPost] using hrun
  have hlocalsMap : targetPost.locals =
      FUPDATE_LIST state.locals (slots.zip (values.map PanWordLab.word)) := by
    simpa [targetPost] using crepRuntimeLocals_zip_eq_fupdateList
      slots values state.locals
  have hupdates :
      FUPDATE_LIST state.locals (slots.zip (values.map PanWordLab.word)) =
        FUPDATE_LIST state.locals
          (payloadSlots.zip ((panValueFlatten payload).map PanWordLab.word)) := by
    rw [← hpayloadSlots, hflatten]
  refine ⟨targetPost, hrunPost, ?_⟩
  rw [hlocalsMap, hupdates]
  exact hlocalsPayload

/-! Arbitrary-payload actual-state handler-entry boundary. It runs the target
`exp_hdl` against the caller/callee states and supplies all four relations
required by the handler-body IH. The recursive callee and handler IHs and the
enclosing HOL `Call_Ret_Exception` induction case remain open. -/
theorem crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceCallerLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (targetCaller targetCallee : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (values : List (RiscV.Word 64))
    (hstate : stateRel sourceAfterCallee targetCallee)
    (hcode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      targetCallee.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context sourceCallerLocals targetCaller.locals)
    (hsource : FLOOKUP sourceCallerLocals name = some old)
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars name = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current,
      (crepRuntimeCallerState targetCaller targetCallee).locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState targetCaller targetCallee) 0 slots values) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (crepRuntimeCallerState targetCaller targetCallee)
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      stateRel
        { sourceAfterCallee with locals := updatePanValueMap sourceCallerLocals name payload }
        targetPost ∧
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      localsRel context
        (updatePanValueMap sourceCallerLocals name payload) targetPost.locals := by
  let targetHandlerStart := crepRuntimeCallerState targetCaller targetCallee
  obtain ⟨targetPost, hrun, hlocalsPost⟩ :=
    crepRuntimeExpHdlFiniteMapWords_localsRel context handler primitive
      targetHandlerStart sourceCallerLocals name shape slots old payload values
      hlocals hsource hshape hvariable hpayloadShape hflatten hslots hglobals
  have hrunExact := crepRuntimeExpHdlFiniteMapWords handler primitive
    targetHandlerStart context.vars name shape slots values hvariable hslots hglobals
  have hpostPair := Option.some.inj (hrun.symm.trans hrunExact)
  have hpost : targetPost =
      { targetHandlerStart with locals := ((slots.zip values).foldl
        (fun locals (entry : Nat × RiscV.Word 64) =>
          updateCrepRuntimeLocal locals entry.1 (.word entry.2))
        targetHandlerStart.locals) } := congrArg Prod.snd hpostPair
  have hsourceUpdate : FUPDATE sourceCallerLocals (name, payload) =
      updatePanValueMap sourceCallerLocals name payload := by
    funext key
    by_cases hkey : name = key
    · subst key
      simp [FUPDATE, updatePanValueMap]
    · have hforward : (name == key) = false := beq_eq_false_iff_ne.mpr hkey
      have hbackward : (key == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm hkey)
      simp [FUPDATE, updatePanValueMap, hforward, hbackward]
  refine ⟨targetPost, hrun, ?_, ?_, hexcp, ?_⟩
  · rw [hpost]
    simpa [stateRel, targetHandlerStart, crepRuntimeCallerState] using hstate
  · rw [hpost]
    simpa [targetHandlerStart, crepRuntimeCallerState] using hcode
  · rw [← hsourceUpdate]
    exact hlocalsPost

/-! Compose the mixed HOL compiled-argument cases, including arbitrary-inner
RField arguments, with the state-owned `code_rel` lookup. Target argument
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
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression)
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
        some (compileProgRiscV
          (PanToCrepProofContext.toHOLContext (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))))
          sourceBody, targetLocals) ∧
      targetLocals = tlcWordLab
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have harguments := compileArgsHOL_constLocalStructAddressOrRFieldInnerIH_eval_flatten
    context source target expressions values hstate hcode hlocals hsupported hsource
  obtain ⟨targetLocals, hlookup, htargetFold⟩ :=
    lookupCrepRuntimeCode_ofCodeRel context source target function parameters
      sourceBody returnShape (values.flatMap panValueFlatten) hcode hentry
      hargumentLength
  have htargetMap : targetLocals = tlcWordLab
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
    calc
      targetLocals = ((List.range
          (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
          (values.flatMap panValueFlatten)).foldl
            (fun locals (slot, word) => updateCrepRuntimeLocal locals slot (.word word))
            (FEMPTY : Nat → Option (PanWordLab (RiscV.Word 64))) := htargetFold
      _ = FUPDATE_LIST FEMPTY
          ((List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
            ((values.flatMap panValueFlatten).map PanWordLab.word)) :=
        crepRuntimeLocals_zip_eq_fupdateList
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
          (values.flatMap panValueFlatten) FEMPTY
      _ = tlcWordLab
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := rfl
  exact ⟨targetLocals, by simpa [compilerContext] using harguments, hlookup,
    htargetMap⟩

/-! Compose a full HOL-shaped expression IH with the real source/target code
maps at Call argument lookup. The flattened target words are obtained by the
`compile_args` induction above, then `code_rel` supplies production
`lookupCrepRuntimeCode`; the remaining Call body IHs are still separate. -/
theorem lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH
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
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExps source expressions = some values)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (values.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
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
          sourceBody, targetLocals) ∧
      targetLocals = tlcWordLab
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
  have harguments := compileArgsHOL_eval_flatten_of_compileExpRel context source
    target expressions values hstate hcode hlocals hlocalized hsource heach
  obtain ⟨targetLocals, hlookup, htargetFold⟩ :=
    lookupCrepRuntimeCode_ofCodeRel context source target function parameters
      sourceBody returnShape (values.flatMap panValueFlatten) hcode hentry
      hargumentLength
  have htargetMap : targetLocals = tlcWordLab
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
    calc
      targetLocals = ((List.range
          (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
          (values.flatMap panValueFlatten)).foldl
            (fun locals (slot, word) => updateCrepRuntimeLocal locals slot (.word word))
            (FEMPTY : Nat → Option (PanWordLab (RiscV.Word 64))) := htargetFold
      _ = FUPDATE_LIST FEMPTY
          ((List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
            ((values.flatMap panValueFlatten).map PanWordLab.word)) :=
        crepRuntimeLocals_zip_eq_fupdateList
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
          (values.flatMap panValueFlatten) FEMPTY
      _ = tlcWordLab
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := rfl
  have hlookupExact :
      lookupCrepRuntimeCode function (values.flatMap panValueFlatten) target.code =
        some (compileProgRiscV
          (PanToCrepProofContext.toHOLContext (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))))
          sourceBody, targetLocals) := by
    simpa [compileCodeRelProg_eq_compileProgRiscV] using hlookup
  exact ⟨targetLocals, harguments, hlookupExact, htargetMap⟩

/-! Derive the actual Call-entry `locals_rel` premise from the successful
state-owned source lookup and the production target code lookup. The source
lookup exposes its real `bindPanValueParameters` result; the target lookup
exposes the exact `tlcWordLab` map. This is the relation boundary for a
recursive callee IH, with no detached locals assumption. -/
theorem lookupCrepRuntimeCode_callEntryLocalsRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length) :
    ∃ targetCalleeLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetCalleeLocals) ∧
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        sourceCalleeLocals targetCalleeLocals := by
  have hmatch := panSemCodeArgumentsMatch_of_lookup_success source.structs
    source.code function parameters arguments sourceBody returnShape
    sourceCalleeLocals hentry hsourceCall
  obtain ⟨hnames, hbind⟩ := bindPanValueParameters_of_lookup_success
    source.structs source.code function parameters arguments sourceBody returnShape
    sourceCalleeLocals hentry hsourceCall
  obtain ⟨targetCalleeLocals, _harguments, htargetLookup, htargetMap⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgs context source target function
      parameters sourceBody returnShape expressions arguments hstate hcode hlocals
      hsupported hsourceArgs hentry hargumentLength
  have hstateForWf := hstate
  obtain ⟨_, _, _, hstructs, _, _, _, _, _, _⟩ := hstate
  have hmatchEmpty : panSemCodeArgumentsMatch [] parameters arguments = true := by
    simpa [hstructs] using hmatch
  have hshapeMapRaw := panSemCodeArgumentsMatch_shapeMapEq [] parameters arguments
    hmatchEmpty
  have hshapeMap : parameters.map Prod.snd = arguments.map panSemShapeOf := by
    calc
      parameters.map Prod.snd = arguments.map (panValueShape []) := hshapeMapRaw
      _ = arguments.map panSemShapeOf :=
        (panSemShapeOfMapPanValueShapeNil arguments).symm
  have hparameterLength := panSemCodeArgumentsMatch_length [] parameters arguments
    hmatchEmpty
  have hvaluesWf := evalPanSemStateExpsWfShapeOfStateRel source target context
    target.locals expressions arguments hsourceArgs hstateForWf hlocals
  have hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true := by
    intro value hmem
    obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hget : arguments[index]? = some value := by
      rw [List.getElem?_eq_getElem hindex, hvalue]
    have hvalueWf := panValueIsWfValues_getElem? hvaluesWf hget
    have hshapeWf := panValueIsWf_isWfShape_panValueShape [] value hvalueWf
    simpa [panSemShapeOf_eq_panValueShape_nil] using hshapeWf
  have hslots :
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).Nodup :=
    List.nodup_range
  have hslotsLength :
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).length =
        (arguments.flatMap panValueFlatten).length := by
    simpa using hargumentLength
  have hlocalsRel := bindPanValueParametersLocalsRelOfPanSem context parameters
    arguments (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
    sourceCalleeLocals hnames hparameterLength hshapeMap hslots hslotsLength hwf hbind
  refine ⟨targetCalleeLocals, htargetLookup, ?_⟩
  simpa [htargetMap] using hlocalsRel

/-! Full-expression-IH variant of the actual Call-entry relation boundary.
It composes the arbitrary `compile_exp_val_rel`-shaped argument IH with the
state-owned source Call lookup and production target code lookup, then proves
the callee `locals_rel` for the real bound source locals and target slot map.
The Call body and handler recursive IHs remain separate. -/
theorem lookupCrepRuntimeCode_callEntryLocalsRel_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals))
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    ∃ targetCalleeLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
            (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetCalleeLocals) ∧
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        sourceCalleeLocals targetCalleeLocals := by
  have hmatch := panSemCodeArgumentsMatch_of_lookup_success source.structs
    source.code function parameters arguments sourceBody returnShape
    sourceCalleeLocals hentry hsourceCall
  obtain ⟨hnames, hbind⟩ := bindPanValueParameters_of_lookup_success
    source.structs source.code function parameters arguments sourceBody returnShape
    sourceCalleeLocals hentry hsourceCall
  have hvaluesWf := evalPanSemStateExpsWfShapeOfStateRel source target context
    target.locals expressions arguments hsourceArgs hstate hlocals
  have hstateForLookup := hstate
  obtain ⟨_, _, _, hstructs, _, _, _, _, _, _⟩ := hstate
  have hmatchEmpty : panSemCodeArgumentsMatch [] parameters arguments = true := by
    simpa [hstructs] using hmatch
  have hargumentLength := panSemCodeArgumentsMatch_flattenLength parameters arguments
    hmatchEmpty hvaluesWf
  obtain ⟨targetCalleeLocals, _harguments, htargetLookup, htargetMap⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH context source target
      function parameters sourceBody returnShape expressions arguments hstateForLookup hcode
      hlocals hlocalized hsourceArgs hentry hargumentLength heach
  have hshapeMapRaw := panSemCodeArgumentsMatch_shapeMapEq [] parameters arguments
    hmatchEmpty
  have hshapeMap : parameters.map Prod.snd = arguments.map panSemShapeOf := by
    calc
      parameters.map Prod.snd = arguments.map (panValueShape []) := hshapeMapRaw
      _ = arguments.map panSemShapeOf :=
        (panSemShapeOfMapPanValueShapeNil arguments).symm
  have hparameterLength := panSemCodeArgumentsMatch_length [] parameters arguments
    hmatchEmpty
  have hwf : ∀ value, value ∈ arguments →
      isWfShape [] (panSemShapeOf value) = true := by
    intro value hmem
    obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hget : arguments[index]? = some value := by
      rw [List.getElem?_eq_getElem hindex, hvalue]
    have hvalueWf := panValueIsWfValues_getElem? hvaluesWf hget
    have hshapeWf := panValueIsWf_isWfShape_panValueShape [] value hvalueWf
    simpa [panSemShapeOf_eq_panValueShape_nil] using hshapeWf
  have hslots :
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).Nodup :=
    List.nodup_range
  have hslotsLength :
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).length =
        (arguments.flatMap panValueFlatten).length := by
    simpa using hargumentLength
  have hlocalsRel := bindPanValueParametersLocalsRelOfPanSem context parameters
    arguments (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
    sourceCalleeLocals hnames hparameterLength hshapeMap hslots hslotsLength hwf hbind
  refine ⟨targetCalleeLocals, htargetLookup, ?_⟩
  simpa [htargetMap] using hlocalsRel

/-! Const/Local specialization of the state-owned Call-entry boundary. It
derives the full expression IH required for target lookup and parameter
locals from the preceding four-conclusion argument-list proof. -/
theorem lookupCrepRuntimeCode_callEntryLocalsRel_constOrLocalOfHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals)) :
    ∃ targetCalleeLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
            (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetCalleeLocals) ∧
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        sourceCalleeLocals targetCalleeLocals := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    cases hsupported expression hmem <;> simp [expGlobalVars]
  obtain ⟨_hcompiledArgs, hperExpression⟩ :=
    compileArgsHOL_constOrLocal_ofHOLIH context source target expressions arguments
      hstate hcode hlocals hsupported hsourceArgs
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL compilerContext expression).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval _hstate _hcode _hlocals hlocalized'
    simpa [compilerContext] using
      hperExpression expression hmem value heval hlocalized'
  exact lookupCrepRuntimeCode_callEntryLocalsRel_ofHOLIH context source target
    function parameters sourceBody returnShape expressions arguments sourceCalleeLocals
    hstate hcode hlocals hlocalized hsourceArgs hentry hsourceCall heach

/-! Actual state-owned Call-entry relation for Const/Local/address arguments
and one-level RStructs over those leaves. It derives the expression IHs and
uses the production source/target code maps for the callee lookup. -/
theorem lookupCrepRuntimeCode_callEntryLocalsRel_constLocalAddressOrStructOfHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalAddressOrStruct expression)
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals)) :
    ∃ targetCalleeLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
            (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetCalleeLocals) ∧
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        sourceCalleeLocals targetCalleeLocals := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    exact compileArgConstLocalAddressOrStruct_localized (hsupported expression hmem)
  obtain ⟨_hcompiledArgs, hperExpression⟩ :=
    compileArgsHOL_constLocalAddressOrStruct_ofHOLIH context source target expressions arguments
      hstate hcode hlocals hsupported hsourceArgs
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL compilerContext expression).1 =
            some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval _hstate _hcode _hlocals hlocalized'
    simpa [compilerContext] using
      hperExpression expression hmem value heval hlocalized'
  exact lookupCrepRuntimeCode_callEntryLocalsRel_ofHOLIH context source target
    function parameters sourceBody returnShape expressions arguments sourceCalleeLocals
    hstate hcode hlocals hlocalized hsourceArgs hentry hsourceCall heach

/-! The caller's state, code, and exception relations survive Call's callee
entry setup: the two evaluators replace only locals and decrement the related
clocks, while both state-owned code maps and the source exception-shape map
remain unchanged. `codeRel` and `excpRel` are carried into HOL's function
context `ctxtFc`; the formal- and flattened-argument `localsRel` in that
context is a separate remaining obligation for full Call induction. -/
theorem panSemCallCalleeEntryStateCodeExcpRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (parameters : List (String × Shape)) (slots : List Nat)
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
    (targetCalleeLocals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hexcp : excpRel context.eids source.exceptionShapes) :
    stateRel
        { { source with locals := sourceCalleeLocals } with
          clock := decPanClock source.clock }
        (decCrepClock { target with locals := targetCalleeLocals }) ∧
      codeRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd) slots)
        (panSemCodeAsLookup
          ({ { source with locals := sourceCalleeLocals } with
            clock := decPanClock source.clock }).code)
        (decCrepClock { target with locals := targetCalleeLocals }).code ∧
      excpRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd) slots).eids
        ({ { source with locals := sourceCalleeLocals } with
          clock := decPanClock source.clock }).exceptionShapes := by
  obtain ⟨hmemory, hmemaddrs, hshared, hstructs, hglobals, hclock, hbe, hffi,
    hbase, htop⟩ := hstate
  refine ⟨?_, ?_, ?_⟩
  · unfold stateRel
    simp only [decCrepClock, decPanClock]
    exact ⟨hmemory, hmemaddrs, hshared, hstructs, hglobals,
      congrArg (fun clock : Nat => clock - 1) hclock,
      hbe, hffi, hbase, htop⟩
  · change codeRel context (panSemCodeAsLookup source.code) target.code
    exact hcode
  · change excpRel context.eids source.exceptionShapes
    exact hexcp

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
      compileArgConstLocalStructAddressOrRFieldInnerIH context source caller expression)
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
  obtain ⟨targetLocals, harguments, hlookup, _htargetMap⟩ :=
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
      compileArgConstLocalStructAddressOrRFieldInnerIH context source caller expression)
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
  obtain ⟨targetLocals, harguments, hlookup, _htargetMap⟩ :=
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
    harguments hlookup hinfoValid hclock hmatch
    (hcalleeIH targetLocals hlookup)
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
      compileArgConstLocalStructAddressOrRFieldInnerIH context source caller expression)
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

/-! Full-expression-IH variant of the actual target Call_Ret_Exception
dispatcher for a one-word payload. `compile_args` evaluation and the target
callee lookup are both derived from the four-conclusion expression IH, after
which the real `exp_hdl` state relation feeds the handler-body IH. The source
Call result and complete `pc_compile_correct` case remain open. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofHOLIH
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
    (sourceCalleeLocals : String → Option (PanValue (RiscV.Word 64)))
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
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals))
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
        handlerBody = some handlerResult)
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  obtain ⟨targetPost, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlOneWord_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable slot
      old value hcalleeState hcalleeCode hexcp hlocals hsource hvariable hslot hglobal
  have hhandlerBody := hhandlerIH targetPost hpayload hpayloadState hpayloadCode
    hpayloadExcp hpayloadLocals
  have hsourceArgsMatch := panSemCodeArgumentsMatch_of_lookup_success source.structs
    source.code function parameters arguments sourceBody returnShape
    sourceCalleeLocals hentry hsourceCall
  have hwfArguments := evalPanSemStateExpsWfShapeOfStateRel source caller context
    caller.locals expressions arguments hsourceArgs hinitialState hlocals
  have hstructs := stateRel_structs source caller hinitialState
  have hsourceArgsMatchEmpty : panSemCodeArgumentsMatch [] parameters arguments = true := by
    simpa [hstructs] using hsourceArgsMatch
  have hargumentLength := panSemCodeArgumentsMatch_flattenLength parameters arguments
    hsourceArgsMatchEmpty hwfArguments
  obtain ⟨targetLocals, harguments, hlookup, _htargetMap⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH context source caller
      function parameters sourceBody returnShape expressions arguments hinitialState
      hcallCode hlocals hlocalized hsourceArgs hentry hargumentLength heach
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
      handlerBody targetLocals calleeState targetPost handlerResult 3 harguments hlookup
      hinfoValid hclock hmatch (hcalleeIH targetLocals hlookup)
      (by simpa [crepRuntimeCallerState] using hpayload) hhandlerBody

/-! Full-expression-IH target Call dispatcher with arbitrary handler payload
length. It derives compiled arguments and the state-owned target callee lookup,
then composes the actual finite-map `exp_hdl` run and all four handler-entry
relations with the handler-body IH. This remains untagged induction support;
the enclosing HOL Call case remains open. -/
private theorem evalCrepRuntimeCall_catchesRaisedHandlerBody_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (values : List (RiscV.Word 64))
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
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars handlerVariable = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current,
      (crepRuntimeCallerState caller calleeState).locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState caller calleeState) 0 slots values)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
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
      evalCrepRuntimeProg handler primitive (values.length + 3)
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hhandlerIH : ∀ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, targetPost) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable payload }
        targetPost →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable payload) targetPost.locals →
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive (slots.length + 4) caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  have hslotsLength := crepRuntimeGlobalWordsRel_length
    (crepRuntimeCallerState caller calleeState) 0 slots values hglobals
  obtain ⟨targetPost, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable shape slots
      old payload values hcalleeState hcalleeCode hexcp hlocals hsource hshape
      hvariable hpayloadShape hflatten hslots hglobals
  have hhandlerBody := hhandlerIH targetPost hpayload hpayloadState hpayloadCode
    hpayloadExcp hpayloadLocals
  obtain ⟨targetLocals, harguments, hlookup, _htargetMap⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH context source caller
      function parameters sourceBody returnShape expressions arguments hinitialState
      hcallCode hlocals hlocalized hsourceArgs hentry hargumentLength heach
  let handlerStart := crepRuntimeCallerState caller calleeState
  have hhandlerBody' : evalCrepRuntimeProg handler primitive (slots.length + 2)
      { targetPost with clock := min handlerStart.clock targetPost.clock }
      handlerBody = some handlerResult := by
    simpa [fixCrepRuntimeClock] using hhandlerBody
  have hpayloadStart : evalCrepRuntimeProg handler primitive (slots.length + 2)
      handlerStart (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, targetPost) := by
    simpa [handlerStart] using hpayload
  have hpayloadStart' : evalCrepRuntimeProg handler primitive (slots.length + 2)
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, targetPost) := by
    simpa [handlerStart, crepRuntimeCallerState] using hpayloadStart
  have hhandlerRun : evalCrepRuntimeProg handler primitive (slots.length + 3)
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody) =
        some handlerResult := by
    simp only [evalCrepRuntimeProg]
    rw [hpayloadStart']
    simp only [fixCrepRuntimeClock]
    rw [hhandlerBody']
  exact evalCrepRuntimeCall_handlesRaisedBody handler primitive (slots.length + 3)
    caller destinations caught exceptionCode
    (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody)
    (compileCodeRelProg
      (ctxtFc context.funcs context.eids
        (parameters.map Prod.fst) (parameters.map Prod.snd)
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
      sourceBody)
    function
    (compileArgsHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expressions)
    (arguments.flatMap panValueFlatten) targetLocals calleeState handlerResult
    harguments hlookup hinfoValid hclock hmatch
    (by simpa [hslotsLength] using hcalleeIH targetLocals hlookup)
    hhandlerRun

/-! Two-word-payload specialization of the arbitrary-length target dispatcher.
This keeps the existing concrete Call slice while allowing its actual runtime
composition to exercise the general `exp_hdl`/locals relation above. -/
private theorem evalCrepRuntimeCall_catchesRaisedTwoWordsHandlerBody_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (slot0 slot1 : Nat)
    (old : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode value0 value1 : RiscV.Word 64)
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
    (hshape : panValueShape [] old = .comb [.one, .one])
    (hvariable : FLOOKUP context.vars handlerVariable =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslot0 : ∃ current, caller.locals slot0 = some current)
    (hslot1 : ∃ current, caller.locals slot1 = some current)
    (hglobal0 : calleeState.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : calleeState.globals (1 : BitVec 5) = some (.word value1))
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
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
      evalCrepRuntimeProg handler primitive 5
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hhandlerIH : ∀ targetPost,
      evalCrepRuntimeProg handler primitive 4
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, targetPost) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable
            (.rStruct [.word value0, .word value1]) }
        targetPost →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable
          (.rStruct [.word value0, .word value1])) targetPost.locals →
      evalCrepRuntimeProg handler primitive 4
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive 6 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  let payload : PanValue (RiscV.Word 64) :=
    .rStruct [.word value0, .word value1]
  have hpayloadShape : panValueShape [] payload = .comb [.one, .one] := by
    simp [payload, panValueShape]
  have hflatten : panValueFlatten payload = [value0, value1] := by
    simp [payload, panValueFlatten, panValueFlattenValues]
  have hslots : ∀ slot, slot ∈ [slot0, slot1] →
      ∃ current, (crepRuntimeCallerState caller calleeState).locals slot = some current := by
    intro slot hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · cases hmem
      simpa [crepRuntimeCallerState] using hslot0
    · rcases hmem with hmem | hmem
      · cases hmem
        simpa [crepRuntimeCallerState] using hslot1
      · simp at hmem
  have hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState caller calleeState) 0 [slot0, slot1]
      [value0, value1] := by
    constructor
    · have hmap := evalCrepRuntimeExp_loadGlob_wordLab
        (crepRuntimeCallerState caller calleeState) (0 : BitVec 5)
      rw [show (crepRuntimeCallerState caller calleeState).globals 0 =
          some (.word value0) by simpa [crepRuntimeCallerState] using hglobal0] at hmap
      simpa using hmap
    · constructor
      · have hmap := evalCrepRuntimeExp_loadGlob_wordLab
          (crepRuntimeCallerState caller calleeState) (1 : BitVec 5)
        rw [show (crepRuntimeCallerState caller calleeState).globals 1 =
            some (.word value1) by simpa [crepRuntimeCallerState] using hglobal1] at hmap
        simpa using hmap
      · trivial
  exact evalCrepRuntimeCall_catchesRaisedHandlerBody_ofHOLIH
    context handler primitive source sourceAfterCallee caller function handlerVariable
    (.comb [.one, .one]) [slot0, slot1] old payload destinations caught exceptionCode
    parameters sourceBody returnShape expressions arguments [value0, value1]
    handlerBody calleeState handlerResult hinitialState hcallCode hcalleeState
    hcalleeCode hexcp hlocals hsource (by
      simpa [payload, panValueShape] using hshape) hvariable hpayloadShape hflatten
    hslots hglobals hlocalized hsourceArgs hentry hargumentLength heach hinfoValid
    hclock hmatch hcalleeIH
    (by simpa [payload] using hhandlerIH)

/-! Compose a state-owned source Call result with the arbitrary-payload target
exception dispatcher. The successful source callee lookup determines target
entry locals, the full expression IH determines compiled arguments, and the
recursive target callee IH supplies the related post-state and state-owned
global words used by the actual finite-map `exp_hdl`. The handler IH supplies
the final post-state relations; recursive simulations remain premises, so
this is not the full HOL `pc_compile_correct[Call_Ret_Exception]` theorem. -/
mutual
private theorem panShapeMatches_self_forSourceCall :
    ∀ shape, panShapeMatches shape shape = true
  | .one => by simp [panShapeMatches]
  | .named _ => by simp [panShapeMatches]
  | .comb shapes => by
      simp only [panShapeMatches]
      exact panShapeListMatches_self_forSourceCall shapes

private theorem panShapeListMatches_self_forSourceCall :
    ∀ shapes, panShapeMatches.panShapeListMatches shapes shapes = true
  | [] => by simp [panShapeMatches.panShapeListMatches]
  | shape :: shapes => by
      simp [panShapeMatches.panShapeListMatches,
        panShapeMatches_self_forSourceCall shape,
        panShapeListMatches_self_forSourceCall shapes]
end

private theorem list_mapM_some_lookup_of_mem {α β : Type _}
    (lookup : α → Option β) {keys : List α} {values : List β}
    (hmap : keys.mapM lookup = some values) :
    ∀ key, key ∈ keys → ∃ value, lookup key = some value := by
  induction keys generalizing values with
  | nil =>
      intro key hmem
      cases hmem
  | cons key keys ih =>
      intro candidate hmem
      simp only [List.mapM_cons] at hmap
      cases hlookup : lookup key with
      | none => simp [hlookup] at hmap
      | some value =>
          cases htail : keys.mapM lookup with
          | none => simp [hlookup, htail] at hmap
          | some tail =>
              simp [hlookup, htail] at hmap
              rcases List.mem_cons.mp hmem with hhead | htailMem
              · subst candidate
                exact ⟨value, hlookup⟩
              · exact ih htail candidate htailMem

/-! Result correspondence carried by the recursive handler IH. This records
the result component of HOL `pc_compile_correct` independently from the
post-state relations: normal/error/timeout/control/return/final-FFI results map
constructor-by-constructor, while raised results use the context's exception
code and the actual target state's `globalsLookup` cells. This is Flapjack-only
induction support and is not tagged as the enclosing HOL theorem. -/
def panToCrepClockResultRel {α σ : Type}
    (context : PanToCrepProofContext α)
    (sourceResult : PanValueFfiClockResult α σ)
    (targetResult : CrepRuntimeStep α σ FfiFinalEvent) : Prop :=
  match sourceResult.1, targetResult.1 with
  | .timeout .., .timeout => True
  | .control (.normal ..), .normal => True
  | .control (.error ..), .error => True
  | .control (.broke ..), .broke 0 => True
  | .control (.continued ..), .continued 0 => True
  | .control (.returned _ _ _ _ values), .returned words =>
      words = values.flatMap panValueFlatten
  | .control (.raised _ _ _ _ exception value), .raised code =>
      FLOOKUP context.eids exception = some code ∧
        (1 ≤ Shape.shapeSize (panSemShapeOf value) →
          globalsLookup targetResult.2 value =
            some ((panValueFlatten value).map PanWordLab.word) ∧
          Shape.shapeSize (panSemShapeOf value) ≤ 32)
  | .control (.finalFfi _ _ _ _ event), .finalFfi targetEvent =>
      targetEvent = event
  | _, _ => False

/-! Compiler-generated function return destinations are a mapped `List.range`,
so the target runtime's duplicate-destination guard follows from function
metadata itself. -/
private theorem allocatedNamesHOL_nodup
    (context : PanToCrepHOLContext α) (shape : Shape) :
    (allocatedNamesHOL context shape).Nodup := by
  unfold allocatedNamesHOL
  apply List.nodup_iff_pairwise_ne.mpr
  exact (List.nodup_iff_pairwise_ne.mp
      (List.nodup_range (n := Shape.shapeSize shape))).map
    (fun offset => context.vmax + 1 + offset)
    (by
      intro left right hne heq
      apply hne
      omega)

theorem crepRuntimeCallInfoValid_functionReturnNamesHOL
    (context : PanToCrepHOLContext α) (function : FunName)
    (handler : Option (α × CrepProg α)) :
    crepRuntimeCallInfoValid
      (some (functionReturnNamesHOL context function, handler)) = true := by
  cases hlookup : FLOOKUP context.funcs function with
  | none => simp [crepRuntimeCallInfoValid, functionReturnNamesHOL, hlookup]
  | some metadata =>
      rcases metadata with ⟨_, shape⟩
      simp only [crepRuntimeCallInfoValid, functionReturnNamesHOL, hlookup]
      apply decide_eq_true
      exact (eraseDups_length_eq_iff_nodup _).2
        (allocatedNamesHOL_nodup context shape)

/-! Compose a production source Call with its recursive callee and handler
    simulation hypotheses for a matching raised payload of any supported shape.
    Both recursive source evaluations use the parent Call's canonical budget
    minus its two dispatch steps; `panSemCodeEvaluateFuel_call_two_le` derives
    the source evaluator fuel equation internally. The relation boundary is
    width-indexed `codeRelW`. This is an untagged induction-case lemma: the
    handler-entry source state is defined from the source call's callee
    globals, memory, FFI state, and minimum clock in the proposition itself;
    callers supply no independent intermediate state or equality premise. The
    enclosing `pc_compile_correct` theorem and its full induction remain open. -/
theorem panSemSourceCall_and_crepTargetCall_catchesRaisedPayload_postRelations
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ)
    (function sourceException handlerVariable : String)
    (handlerProgram : Prog (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64)))
    (payload : PanValue (RiscV.Word 64))
    (values : List (RiscV.Word 64))
    (shape : Shape)
    (old : PanValue (RiscV.Word 64))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (parameters : List (String × Shape))
    (arguments : List (PanValue (RiscV.Word 64)))
    (sourceCalleeLocals calleeRaisedLocals calleeGlobals :
      String → Option (PanValue (RiscV.Word 64)))
    (calleeMemory : (RiscV.Word 64) → Option (PanValue (RiscV.Word 64)))
    (calleeFfi : FfiState σ) (calleeClock : Nat)
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (slots : List Nat) (destinations : List Nat)
    (caught exceptionCode : RiscV.Word 64)
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (hsourceCalleeBody : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, handlerProgram)))
          function expressions) - 2) sourceCalleeLocals
      source.globals source.memory source.ffi (decPanClock source.clock) sourceBody
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
        some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory calleeFfi
        sourceException payload), calleeClock))
    (hsourceHandlerBody : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, handlerProgram)))
          function expressions) - 2)
      (updatePanValueMap source.locals handlerVariable payload)
      calleeGlobals calleeMemory calleeFfi
      (min (decPanClock source.clock) calleeClock) handlerProgram
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some sourceResult)
    (hsourceHandlerLocal : FLOOKUP source.locals handlerVariable = some old)
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hcontextException : FLOOKUP context.eids sourceException = some exceptionCode)
    (hinitialState : stateRel source caller)
    (hcallCode : codeRelW 64 context (panSemCodeAsLookup source.code) caller.code)
    (hexcp : excpRel context.eids source.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hvariable : FLOOKUP context.vars handlerVariable = some (shape, slots))
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hsourceCall : lookupPanSemCodeCall source.structs source.code function arguments =
      some (sourceBody, returnShape, sourceCalleeLocals))
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
    (hdestinations : destinations =
      functionReturnNamesHOL context.toHOLContext function)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    :
    let sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ) :=
      { { { { source with globals := calleeGlobals } with memory := calleeMemory }
        with ffi := calleeFfi }
        with clock := min (decPanClock source.clock) calleeClock }
    (hsourceExceptionShape : sourceAfterCallee.exceptionShapes sourceException =
      some shape) →
    (hcalleeTargetIH :
      sourceAfterCallee.exceptionShapes sourceException = some shape →
      FLOOKUP context.eids sourceException = some exceptionCode →
      (evalPanValueFfiClockCodeProg sourceContext sourcePrimitive sourceHandler
        source.structs source.code source.exceptionShapes source.baseAddress
        source.topAddress panSemBitVec64BytesInWord
        (panSemCodeEvaluateFuel source
          (.call (some (none, some (sourceException, handlerVariable, handlerProgram)))
            function expressions) - 2) sourceCalleeLocals
        source.globals source.memory source.ffi (decPanClock source.clock) sourceBody
        (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
        some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory calleeFfi
          sourceException payload), calleeClock)) →
      ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      stateRel
        ({ { source with locals := sourceCalleeLocals } with
          clock := decPanClock source.clock })
        (decCrepClock { caller with locals := targetLocals }) →
      codeRelW 64
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        (panSemCodeAsLookup source.code) caller.code →
      excpRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))).eids
        source.exceptionShapes →
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        sourceCalleeLocals targetLocals →
      evalCrepRuntimeProg handler primitive (values.length + 3)
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState) ∧
      stateRel sourceAfterCallee calleeState ∧
      codeRelW 64 context (panSemCodeAsLookup sourceAfterCallee.code) calleeState.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      crepRuntimeGlobalWordsRel
        (crepRuntimeCallerState caller calleeState) 0 slots values) →
    (hhandlerIH : ∀ targetPost,
      evalPanValueFfiClockCodeProg sourceContext sourcePrimitive sourceHandler
        source.structs source.code source.exceptionShapes source.baseAddress
        source.topAddress panSemBitVec64BytesInWord
        (panSemCodeEvaluateFuel source
          (.call (some (none, some (sourceException, handlerVariable, handlerProgram)))
            function expressions) - 2)
        (updatePanValueMap source.locals handlerVariable payload)
        calleeGlobals calleeMemory calleeFfi
        (min (decPanClock source.clock) calleeClock) handlerProgram
        (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some sourceResult →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable
            payload }
        targetPost →
      codeRelW 64 context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable payload) targetPost.locals →
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        (compileCodeRelProg context handlerProgram) = some handlerResult ∧
      stateRel (panSemCodeStateAfter source sourceResult) handlerResult.2 ∧
      codeRelW 64 context
        (panSemCodeAsLookup (panSemCodeStateAfter source sourceResult).code)
        handlerResult.2.code ∧
      excpRel context.eids
        (panSemCodeStateAfter source sourceResult).exceptionShapes ∧
      localsRel context (panSemCodeStateAfter source sourceResult).locals
        handlerResult.2.locals ∧
      panToCrepClockResultRel context sourceResult handlerResult) →
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      source
      (.call (some (none, some (sourceException, handlerVariable, handlerProgram)))
        function expressions) = some sourceResult ∧
    evalCrepRuntimeCall handler primitive (slots.length + 4) caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (compileCodeRelProg context handlerProgram)))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult ∧
    stateRel (panSemCodeStateAfter source sourceResult) handlerResult.2 ∧
    codeRelW 64 context
      (panSemCodeAsLookup (panSemCodeStateAfter source sourceResult).code)
      handlerResult.2.code ∧
    excpRel context.eids
      (panSemCodeStateAfter source sourceResult).exceptionShapes ∧
    localsRel context (panSemCodeStateAfter source sourceResult).locals
      handlerResult.2.locals ∧
    panToCrepClockResultRel context sourceResult handlerResult := by
  intro sourceAfterCallee hsourceExceptionShape hcalleeTargetIH hhandlerIH
  have hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable)
          (compileCodeRelProg context handlerProgram)))) = true := by
    rw [hdestinations]
    exact crepRuntimeCallInfoValid_functionReturnNamesHOL context.toHOLContext function
      (some (caught, .seq (expHdlFiniteMap context.vars handlerVariable)
        (compileCodeRelProg context handlerProgram)))
  have hsourceExceptionShape' : source.exceptionShapes sourceException = some shape := by
    simpa [sourceAfterCallee] using hsourceExceptionShape
  have hsourceStructs := stateRel_structs source caller hinitialState
  obtain ⟨handlerSlots, handlerWords, hsourceVariableShape, hsourceHandlerWords,
      _hsourceHandlerFlatten, _hsourceHandlerShapeWf⟩ :=
    hlocals.2.2 handlerVariable old hsourceHandlerLocal
  have hsourceVariablePair : (panValueShape [] old, handlerSlots) = (shape, slots) :=
    Option.some.inj (hsourceVariableShape.symm.trans hvariable)
  have hsourceVariableShapeEq : panValueShape [] old = shape := by
    exact congrArg Prod.fst hsourceVariablePair
  have hhandlerSlotsEq : handlerSlots = slots :=
    congrArg Prod.snd hsourceVariablePair
  have hslots : ∀ slot, slot ∈ slots →
      ∃ current, (crepRuntimeCallerState caller calleeState).locals slot = some current := by
    intro slot hslot
    have hslot' : slot ∈ handlerSlots := by
      simpa [hhandlerSlotsEq] using hslot
    obtain ⟨current, hcurrent⟩ :=
      list_mapM_some_lookup_of_mem (FLOOKUP caller.locals) hsourceHandlerWords slot hslot'
    exact ⟨current, by simpa [crepRuntimeCallerState, FLOOKUP] using hcurrent⟩
  have hshape : panValueShape [] old = panValueShape [] payload := by
    rw [hsourceVariableShapeEq, hpayloadShape]
  have hsourceShapeMatch : panShapeMatches
      (panValueShape source.structs payload) shape = true := by
    rw [hsourceStructs, hpayloadShape]
    exact panShapeMatches_self_forSourceCall shape
  have hsourceHandlerAssignment : panValueAssignmentValid source.structs source.locals
      (fun _ => none) .local handlerVariable payload = true := by
    have hsourceHandlerLookup : source.locals handlerVariable = some old := by
      simpa [FLOOKUP] using hsourceHandlerLocal
    unfold panValueAssignmentValid
    rw [hsourceStructs, hsourceHandlerLookup]
    change panShapeMatches (panValueShape [] payload) (panValueShape [] old) = true
    rw [hsourceVariableShapeEq, hpayloadShape]
    exact panShapeMatches_self_forSourceCall shape
  have hsourceClock : source.clock ≠ 0 := by
    rcases hinitialState with ⟨_, _, _, _, _, hclockRel, _, _, _, _⟩
    intro hzero
    apply hclock
    simpa [hclockRel] using hzero
  have hsourceRun := panSemEvaluateRiscV64CodeState_call_catchesRaisedBody_ofState
    sourceContext sourcePrimitive sourceHandler source function sourceException
    handlerVariable expressions arguments returnShape sourceBody sourceCalleeLocals
    calleeRaisedLocals calleeGlobals calleeMemory calleeFfi payload calleeClock
    handlerProgram sourceResult hsourceArgs hsourceCall hsourceClock
    hsourceCalleeBody ⟨shape, hsourceExceptionShape', hsourceShapeMatch⟩
    hsourceHandlerAssignment hsourceHandlerBody
  have hsourceCallRun := hsourceRun.1
  have hargumentLength := by
    have hsourceArgsMatch := panSemCodeArgumentsMatch_of_lookup_success source.structs
      source.code function parameters arguments sourceBody returnShape
      sourceCalleeLocals hentry hsourceCall
    have hwfArguments := evalPanSemStateExpsWfShapeOfStateRel source caller context
      caller.locals expressions arguments hsourceArgs hinitialState hlocals
    have hstructs := stateRel_structs source caller hinitialState
    have hsourceArgsMatchEmpty : panSemCodeArgumentsMatch [] parameters arguments = true := by
      simpa [hstructs] using hsourceArgsMatch
    exact panSemCodeArgumentsMatch_flattenLength parameters arguments
      hsourceArgsMatchEmpty hwfArguments
  obtain ⟨targetLocals, htargetLookup, hcalleeEntryLocals⟩ :=
    lookupCrepRuntimeCode_callEntryLocalsRel_ofHOLIH context source caller function
      parameters sourceBody returnShape expressions arguments sourceCalleeLocals
      hinitialState hcallCode hlocals hlocalized hsourceArgs hentry hsourceCall heach
  obtain ⟨hcalleeEntryState, hcalleeEntryCode, hcalleeEntryExcp⟩ :=
    panSemCallCalleeEntryStateCodeExcpRel context source caller parameters
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
      sourceCalleeLocals targetLocals hinitialState hcallCode hexcp
  obtain ⟨hcalleeRun, hcalleeStateRel, hcalleeCodeRel, hcalleeExcpRel,
      hcalleeGlobals⟩ :=
    hcalleeTargetIH hsourceExceptionShape hcontextException hsourceCalleeBody targetLocals
      htargetLookup hcalleeEntryState
      ((codeRelW_iff_codeRel 64 _ _ _).mpr
        (by simpa [decCrepClock] using hcalleeEntryCode))
      (by simpa using hcalleeEntryExcp) hcalleeEntryLocals
  have hcalleeIH : ∀ targetLocals',
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals') →
      evalCrepRuntimeProg handler primitive (values.length + 3)
        (decCrepClock { caller with locals := targetLocals' })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState) := by
    intro targetLocals' hlookup'
    have hsame : targetLocals' = targetLocals := by
      have htuple := Option.some.inj (hlookup'.symm.trans htargetLookup)
      exact congrArg Prod.snd htuple
    simpa [hsame] using hcalleeRun
  obtain ⟨targetPost, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable shape slots
      old payload values hcalleeStateRel hcalleeCodeRel hcalleeExcpRel hlocals
      hsourceHandlerLocal hshape hvariable hpayloadShape hflatten hslots hcalleeGlobals
  obtain ⟨hhandlerRun, hpostState, hpostCode, hpostExcp, hpostLocals,
      hpostResult⟩ :=
    hhandlerIH targetPost hsourceHandlerBody hpayloadState hpayloadCode hpayloadExcp
      hpayloadLocals
  have htarget := evalCrepRuntimeCall_catchesRaisedHandlerBody_ofHOLIH
    context handler primitive source sourceAfterCallee caller function handlerVariable
    shape slots old payload destinations caught exceptionCode
    parameters sourceBody returnShape expressions arguments values
    (compileCodeRelProg context handlerProgram)
    calleeState handlerResult hinitialState hcallCode hcalleeStateRel hcalleeCodeRel
    hcalleeExcpRel hlocals hsourceHandlerLocal hshape hvariable hpayloadShape hflatten
    hslots hcalleeGlobals hlocalized hsourceArgs hentry
    hargumentLength heach hinfoValid hclock hmatch hcalleeIH
    (fun targetPost' _hrun hstate' hcode' hexcp' hlocals' =>
      (hhandlerIH targetPost' hsourceHandlerBody hstate' hcode' hexcp' hlocals').1)
  exact ⟨hsourceCallRun, htarget,
    hpostState, hpostCode, hpostExcp, hpostLocals, hpostResult⟩

/-! Preserve the handler-body post-state IH through the production target Call
dispatcher. `sourcePost` is the source state supplied by that IH (in a full
Call proof, the projection of the actual source Call result); this helper does
not assume a target run or assert the enclosing compiled-program theorem. -/
theorem evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofCodeRelArgs_postRelations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourcePost : PanSemState (RiscV.Word 64) (FfiState σ))
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
    (hstate : stateRel source caller)
    (hcode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hcalleeState : stateRel sourceAfterCallee calleeState)
    (hcalleeCode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      calleeState.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hsource : FLOOKUP source.locals handlerVariable = some old)
    (hvariable : FLOOKUP context.vars handlerVariable = some (Shape.one, [slot]))
    (hslot : ∃ current, caller.locals slot = some current)
    (hglobal : calleeState.globals (0 : BitVec 5) = some (.word value))
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalStructAddressOrRFieldInnerIH context source caller expression)
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
    (hhandlerIH : ∀ payloadState,
      evalCrepRuntimeProg handler primitive 3
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, payloadState) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable (.word value) }
        payloadState →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) payloadState.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable (.word value)) payloadState.locals →
      evalCrepRuntimeProg handler primitive 3
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, payloadState)).2
        handlerBody = some handlerResult ∧
      stateRel sourcePost handlerResult.2 ∧
      codeRel context (panSemCodeAsLookup sourcePost.code) handlerResult.2.code ∧
      excpRel context.eids sourcePost.exceptionShapes ∧
      localsRel context sourcePost.locals handlerResult.2.locals) :
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult ∧
    stateRel sourcePost handlerResult.2 ∧
    codeRel context (panSemCodeAsLookup sourcePost.code) handlerResult.2.code ∧
    excpRel context.eids sourcePost.exceptionShapes ∧
    localsRel context sourcePost.locals handlerResult.2.locals := by
  obtain ⟨targetPayload, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlOneWord_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable slot old value
      hcalleeState hcalleeCode hexcp hlocals hsource hvariable hslot hglobal
  obtain ⟨hbody, hpostState, hpostCode, hpostExcp, hpostLocals⟩ :=
    hhandlerIH targetPayload hpayload hpayloadState hpayloadCode
      hpayloadExcp hpayloadLocals
  have hcall := evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofCodeRelArgs_relations
    context handler primitive source sourceAfterCallee caller function handlerVariable
    slot old destinations caught exceptionCode value parameters sourceBody returnShape
    expressions arguments handlerBody calleeState handlerResult hstate hcode
    hcalleeState hcalleeCode hexcp hlocals hsource hvariable hslot hglobal
    hsupported hsourceArgs hentry hargumentLength hinfoValid hclock hmatch hcalleeIH
    (fun targetPayload' hpayload' hpayloadState' hpayloadCode' hpayloadExcp'
        hpayloadLocals' =>
      (hhandlerIH targetPayload' hpayload' hpayloadState' hpayloadCode'
        hpayloadExcp' hpayloadLocals').1)
  exact ⟨hcall, hpostState, hpostCode, hpostExcp, hpostLocals⟩

/-! Join production source Call evaluation to the relation-aware target Call
dispatcher. The post-state relation required by the target handler-body IH is
now indexed by the actual source evaluator result, projected through
`panSemCodeStateAfter`; the source run uses the state-owned code map and the
RISC-V state-derived memory inputs. It derives that run from the source
callee-body and handler-body premises. The premise `hcalleeTargetBodyIH`
applies the callee induction hypothesis to the source body run and the
callee-entry relations derived from the actual code lookups; its conclusion
provides the target callee-body run and post-state, code, exception, and
payload-global facts needed by `exp_hdl`. The relation-aware handler IH also
provides its target result and post-state relations. The target destination list
is tied to `functionReturnNamesHOL`; runtime call-info validity is derived from
that metadata. The recursive body simulations remain induction premises, so
this is a Call-case composition step, not the complete
`pc_compile_correct[Call_Ret_Exception]` theorem. -/
theorem panSemSourceCall_and_crepTargetCall_catchesRaisedOneWord_postRelations
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : String)
    (sourceHandlerBody : Prog (RiscV.Word 64))
    (sourceBody : Prog (RiscV.Word 64))
    (returnShape : Shape)
    (sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ)
    (sourceException handlerVariable : String)
    (sourceExpressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (value : RiscV.Word 64)
    (calleeLocals calleeRaisedLocals calleeGlobals :
      VarName → Option (PanValue (RiscV.Word 64)))
    (calleeMemory : (RiscV.Word 64) → Option (PanValue (RiscV.Word 64)))
    (calleeFfi : FfiState σ) (calleeClock : Nat)
    (hsourceCallee : lookupPanSemCodeCall source.structs source.code function
      arguments = some (sourceBody, returnShape, calleeLocals))
    (hsourceClock : source.clock ≠ 0)
    (hsourceCalleeBody : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, sourceHandlerBody)))
          function sourceExpressions) - 2) calleeLocals source.globals
      source.memory source.ffi (decPanClock source.clock) sourceBody
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory calleeFfi
        sourceException (.word value)), calleeClock))
    (hsourceExceptionShape : ∃ shape,
      source.exceptionShapes sourceException = some shape ∧
      panShapeMatches (panValueShape source.structs (.word value)) shape = true)
    (hsourceHandlerBodyRun : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, sourceHandlerBody)))
          function sourceExpressions) - 2)
      (updatePanValueMap source.locals handlerVariable (.word value))
      calleeGlobals calleeMemory calleeFfi (min (decPanClock source.clock) calleeClock)
      sourceHandlerBody
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some sourceResult)
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (hsourceAfterCallee : sourceAfterCallee =
      { { { { source with globals := calleeGlobals } with memory := calleeMemory }
          with ffi := calleeFfi }
        with clock := min (decPanClock source.clock) calleeClock })
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerVariableTarget : String) (slot : Nat)
    (old : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode : RiscV.Word 64)
    (parameters : List (String × Shape))
    
    (expressions : List (Exp (RiscV.Word 64)))
    (handlerBody : CrepProg (RiscV.Word 64))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (hsourceExpressions : sourceExpressions = expressions)
    (hsourceExceptionCode : FLOOKUP context.eids sourceException = some caught)
    (hsourceHandlerVariable : handlerVariable = handlerVariableTarget)
    (hcompiledHandlerBody : compileCodeRelProg context sourceHandlerBody = handlerBody)
    (hstate : stateRel source caller)
    (hcode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hexcp : excpRel context.eids source.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hsource : FLOOKUP source.locals handlerVariableTarget = some old)
    (hvariable : FLOOKUP context.vars handlerVariableTarget =
      some (Shape.one, [slot]))
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
    (hdestinations : destinations =
      functionReturnNamesHOL context.toHOLContext function)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    (hcalleeTargetBodyIH : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, sourceHandlerBody)))
          function sourceExpressions) - 2) calleeLocals source.globals
      source.memory source.ffi (decPanClock source.clock) sourceBody
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory calleeFfi
        sourceException (.word value)), calleeClock) →
      ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      stateRel
        ({ { source with locals := calleeLocals } with
          clock := decPanClock source.clock })
        (decCrepClock { caller with locals := targetLocals }) →
      codeRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        (panSemCodeAsLookup source.code) caller.code →
      excpRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))).eids
        source.exceptionShapes →
      localsRel
        (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
          (parameters.map Prod.snd)
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
        calleeLocals targetLocals →
      evalCrepRuntimeProg handler primitive 4
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState) ∧
      stateRel sourceAfterCallee calleeState ∧
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) calleeState.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      calleeState.globals (0 : BitVec 5) = some (.word value))
    (hhandlerIH : evalPanValueFfiClockCodeProg sourceContext sourcePrimitive
      sourceHandler source.structs source.code source.exceptionShapes source.baseAddress
      source.topAddress panSemBitVec64BytesInWord
      (panSemCodeEvaluateFuel source
        (.call (some (none, some (sourceException, handlerVariable, sourceHandlerBody)))
          function sourceExpressions) - 2)
      (updatePanValueMap source.locals handlerVariable (.word value))
      calleeGlobals calleeMemory calleeFfi (min (decPanClock source.clock) calleeClock)
      sourceHandlerBody
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some sourceResult →
      sourceExpressions = expressions →
      FLOOKUP context.eids sourceException = some caught →
      handlerVariable = handlerVariableTarget →
      compileCodeRelProg context sourceHandlerBody = handlerBody →
      ∀ payloadState,
      evalCrepRuntimeProg handler primitive 3
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariableTarget) =
          some (.normal, payloadState) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariableTarget (.word value) }
        payloadState →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) payloadState.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariableTarget (.word value))
        payloadState.locals →
      evalCrepRuntimeProg handler primitive 3
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, payloadState)).2
        handlerBody = some handlerResult ∧
      stateRel (panSemCodeStateAfter source sourceResult) handlerResult.2 ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter source sourceResult).code)
        handlerResult.2.code ∧
      excpRel context.eids
        (panSemCodeStateAfter source sourceResult).exceptionShapes ∧
      localsRel context (panSemCodeStateAfter source sourceResult).locals
        handlerResult.2.locals) :
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      source
      (.call (some (none, some (sourceException, handlerVariable, sourceHandlerBody)))
        function sourceExpressions) = some sourceResult ∧
    evalCrepRuntimeCall handler primitive 5 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariableTarget) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult ∧
    stateRel (panSemCodeStateAfter source sourceResult) handlerResult.2 ∧
    codeRel context
      (panSemCodeAsLookup (panSemCodeStateAfter source sourceResult).code)
      handlerResult.2.code ∧
    excpRel context.eids
      (panSemCodeStateAfter source sourceResult).exceptionShapes ∧
    localsRel context (panSemCodeStateAfter source sourceResult).locals
        handlerResult.2.locals := by
  have hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariableTarget) handlerBody))) = true := by
    rw [hdestinations]
    exact crepRuntimeCallInfoValid_functionReturnNamesHOL context.toHOLContext function
      (some (caught, .seq (expHdlFiniteMap context.vars handlerVariableTarget) handlerBody))
  have hsourceHandlerLookup : source.locals handlerVariableTarget = some old := by
    simpa [FLOOKUP] using hsource
  have hsourceHandlerCallLookup : source.locals handlerVariable = some old := by
    simpa [hsourceHandlerVariable] using hsourceHandlerLookup
  obtain ⟨names, words, hsourceVariableShape, _hsourceWords, _hsourceFlatten,
      _hsourceShapeWf⟩ := hlocals.2.2 handlerVariableTarget old hsource
  have hsourceVariablePair : (panValueShape [] old, names) = (Shape.one, [slot]) :=
    Option.some.inj (hsourceVariableShape.symm.trans hvariable)
  have hsourceVariableShapeEq : panValueShape [] old = Shape.one := by
    exact congrArg Prod.fst hsourceVariablePair
  have hslotNamesEq : names = [slot] := congrArg Prod.snd hsourceVariablePair
  have hslot : ∃ current, caller.locals slot = some current := by
    have hslotMem : slot ∈ names := by simp [hslotNamesEq]
    obtain ⟨current, hcurrent⟩ :=
      list_mapM_some_lookup_of_mem (FLOOKUP caller.locals) _hsourceWords slot hslotMem
    exact ⟨current, by simpa [FLOOKUP] using hcurrent⟩
  have hsourceStructs := stateRel_structs source caller hstate
  have hsourceHandlerAssignment : panValueAssignmentValid source.structs source.locals
      (fun _ => none) .local handlerVariable (.word value) = true := by
    unfold panValueAssignmentValid
    rw [hsourceStructs, hsourceHandlerCallLookup]
    simp [panValueShape, panShapeMatches, hsourceVariableShapeEq]
  have hsourceArguments : evalPanSemStateExps source sourceExpressions = some arguments := by
    simpa [hsourceExpressions] using hsourceArgs
  have hsourceRun := panSemEvaluateRiscV64CodeState_call_catchesRaisedBody_ofState
    sourceContext sourcePrimitive sourceHandler source function sourceException
        handlerVariable sourceExpressions arguments returnShape sourceBody calleeLocals
    calleeRaisedLocals calleeGlobals calleeMemory calleeFfi (.word value) calleeClock
    sourceHandlerBody sourceResult hsourceArguments hsourceCallee hsourceClock
    hsourceCalleeBody hsourceExceptionShape hsourceHandlerAssignment hsourceHandlerBodyRun
  subst sourceAfterCallee
  let sourceAfterCallee :=
    { { { { source with globals := calleeGlobals } with memory := calleeMemory }
      with ffi := calleeFfi }
    with clock := min (decPanClock source.clock) calleeClock }
  obtain ⟨targetLocals, htargetLookup, hcalleeEntryLocals⟩ :=
    lookupCrepRuntimeCode_callEntryLocalsRel_ofHOLIH context source caller function
      parameters sourceBody returnShape expressions arguments calleeLocals
      hstate hcode hlocals hlocalized hsourceArgs hentry hsourceCallee heach
  obtain ⟨hcalleeStateEntry, hcalleeCodeEntry, hcalleeExcpEntry⟩ :=
    panSemCallCalleeEntryStateCodeExcpRel context source caller parameters
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
      calleeLocals targetLocals hstate hcode hexcp
  obtain ⟨_hcalleeTargetRun, hcalleeState, hcalleeCode, hexcp, hglobal⟩ :=
    hcalleeTargetBodyIH hsourceCalleeBody targetLocals htargetLookup
      hcalleeStateEntry hcalleeCodeEntry hcalleeExcpEntry hcalleeEntryLocals
  have hcalleeIH : ∀ targetLocals',
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals') →
      evalCrepRuntimeProg handler primitive 4
        (decCrepClock { caller with locals := targetLocals' })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState) := by
    intro targetLocals' hlookup'
    have hsame : targetLocals' = targetLocals := by
      have htuple := Option.some.inj (hlookup'.symm.trans htargetLookup)
      exact congrArg Prod.snd htuple
    obtain ⟨hstateEntry', hcodeEntry', hexcpEntry'⟩ :=
      panSemCallCalleeEntryStateCodeExcpRel context source caller parameters
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
        calleeLocals targetLocals' hstate hcode hexcp
    exact (hcalleeTargetBodyIH hsourceCalleeBody targetLocals' hlookup'
      hstateEntry' hcodeEntry' hexcpEntry'
      (by simpa [hsame] using hcalleeEntryLocals)).1
  obtain ⟨payloadState, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlOneWord_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariableTarget slot
      old value hcalleeState hcalleeCode hexcp hlocals hsource hvariable hslot hglobal
  have hhandlerPost := hhandlerIH hsourceHandlerBodyRun hsourceExpressions
    hsourceExceptionCode hsourceHandlerVariable hcompiledHandlerBody payloadState
    hpayload hpayloadState hpayloadCode hpayloadExcp hpayloadLocals
  have htarget :=
    evalCrepRuntimeCall_catchesRaisedOneWordHandlerBody_ofHOLIH
      context handler primitive source sourceAfterCallee caller function
      handlerVariableTarget slot old destinations caught exceptionCode value
      parameters sourceBody returnShape expressions arguments calleeLocals handlerBody
      calleeState handlerResult hstate hcode hcalleeState hcalleeCode hexcp hlocals
      hsource hvariable hslot hglobal hlocalized hsourceArgs hentry hsourceCallee
      hinfoValid hclock hmatch hcalleeIH
      (fun targetPost hpost hpstate pcode pexcp plocals =>
        (hhandlerIH hsourceHandlerBodyRun hsourceExpressions hsourceExceptionCode
          hsourceHandlerVariable hcompiledHandlerBody targetPost hpost hpstate pcode
          pexcp plocals).1)
      heach
  obtain ⟨htargetRun, hstatePost, hcodePost, hexcpPost, hlocalsPost⟩ := hhandlerPost
  exact ⟨hsourceRun.1, htarget, hstatePost, hcodePost, hexcpPost, hlocalsPost⟩

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
      setCrepHolGlobals, CrepRuntimeState.toHolState,
      updateCrepRuntimeGlobal_eq_FUPDATE,
      clearCrepRuntimeLocals, panTheWord]
  have hcallerSlot : ∃ old, targetCaller.locals slot = some old := by
    by_cases heq : (returnSlot == slot)
    · exact ⟨.word 0, by simp [targetCaller, updateCrepRuntimeLocal, heq]⟩
    · exact ⟨.word oldValue,
        by simp [targetCaller, updateCrepRuntimeLocal, heq, htargetSlot]⟩
  have hreturnNames :
      functionReturnNamesHOL context.toHOLContext function = [returnSlot] := by
    simp [functionReturnNamesHOL, returnSlot, allocatedNamesHOL, hfunction,
      PanToCrepProofContext.toHOLContext]
  have hcallInfo : crepRuntimeCallInfoValid
      (some ([returnSlot], some (exceptionCode, continuation)) :
        Option (List Nat × Option ((RiscV.Word 64) × CrepProg (RiscV.Word 64)))) = true := by
    simpa [hreturnNames] using
      crepRuntimeCallInfoValid_functionReturnNamesHOL context.toHOLContext function
        (some (exceptionCode, continuation))
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
    simp only [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
      setCrepRuntimeLocal_eq_update]
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
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCode,
      FUPDATE_LIST]
    funext key
    rfl
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
      setCrepRuntimeGlobals, setCrepHolGlobals, CrepRuntimeState.toHolState,
      updateCrepRuntimeGlobal_eq_FUPDATE, panTheWord]
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
