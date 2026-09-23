import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Proofs.PanToCrep.EvaluatorBoundary
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem

/-!
Constructor-case evaluator equations used by the `pc_compile_correct`
evaluation induction. These are Flapjack proof infrastructure: the HOL script
proves the cases inside `pc_compile_correct` and does not export these Lean
lemmas as standalone declarations.
-/

namespace Flapjack

/-- HOL's `pc_compile_correct[Skip]` source-side evaluator equation, exposed
for reuse in the main evaluation induction. -/
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

/-- HOL's `pc_compile_correct[Skip]` target-side evaluator equation. -/
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

/-- HOL's compiler leaves `Skip` unchanged. -/
theorem compileProgHOL_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) :
    compileProgHOL context .skip = .skip := rfl

/-- HOL's `pc_compile_correct[Break]` source-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Continue]` source-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Annot]` source-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Tick]` source-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Tick]` target-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Break]` target-side evaluator equation. -/
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

/-- HOL's `pc_compile_correct[Continue]` target-side evaluator equation. -/
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

/-- The `Skip` constructor satisfies the concrete source-run-implies-target-run
goal. The target run is constructed here; only clock agreement is needed
because both evaluators leave their runtime states unchanged. -/
theorem panToCrepConcreteEvaluationGoal_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ)
    (hclock : sourceState.legacy.clock = targetState.clock)
    (hfuel : 0 < fuel) :
    panToCrepConcreteEvaluationGoal context sourceCode targetCode
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      fuel sourceState targetState .skip := by
  intro _hruntime sourceRun hsource
  have hsourceSkip :
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState .skip =
      some (.control (.normal sourceState.legacy.locals sourceState.legacy.globals
        sourceState.legacy.memory sourceState.legacy.ffi), sourceState.legacy.clock) := by
    simp [panToCrepSourceEvaluate, panSemEvaluateExactState, panSemEvaluate,
      panSemEvaluateWithFuel, panSemEvaluateFuel, PanSemExactState.toEvaluateState,
      evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  rw [hsourceSkip] at hsource
  injection hsource with hrun
  subst sourceRun
  cases fuel with
  | zero => omega
  | succ fuel =>
      refine ⟨((CrepRuntimeResult.normal : CrepRuntimeResult α FfiFinalEvent),
        targetState), ?_, ?_⟩
      · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
          evalCrepRuntimeResult, evalCrepRuntimeProg]
      · simp [panToCrepRunResultRel, panToCrepControlResultRel, hclock]

/-- The `Break` constructor satisfies the concrete source-run-implies-target-run
goal; the HOL result relation maps the source break to target label zero. -/
theorem panToCrepConcreteEvaluationGoal_break
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ)
    (hclock : sourceState.legacy.clock = targetState.clock)
    (hfuel : 0 < fuel) :
    panToCrepConcreteEvaluationGoal context sourceCode targetCode
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      fuel sourceState targetState .break := by
  intro _hruntime sourceRun hsource
  have hsourceBreak :
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState .break =
      some (.control (.broke sourceState.legacy.locals sourceState.legacy.globals
        sourceState.legacy.memory sourceState.legacy.ffi), sourceState.legacy.clock) := by
    simp [panToCrepSourceEvaluate, panSemEvaluateExactState, panSemEvaluate,
      panSemEvaluateWithFuel, panSemEvaluateFuel, PanSemExactState.toEvaluateState,
      evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  rw [hsourceBreak] at hsource
  injection hsource with hrun
  subst sourceRun
  cases fuel with
  | zero => omega
  | succ fuel =>
      refine ⟨((CrepRuntimeResult.broke 0 : CrepRuntimeResult α FfiFinalEvent),
        targetState), ?_, ?_⟩
      · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
          evalCrepRuntimeResult, evalCrepRuntimeProg]
      · simp [panToCrepRunResultRel, panToCrepControlResultRel, hclock]

/-- The `Continue` constructor satisfies the concrete source-run-implies-
target-run goal with the HOL level-zero result mapping. -/
theorem panToCrepConcreteEvaluationGoal_continue
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ)
    (hclock : sourceState.legacy.clock = targetState.clock)
    (hfuel : 0 < fuel) :
    panToCrepConcreteEvaluationGoal context sourceCode targetCode
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      fuel sourceState targetState .continue := by
  intro _hruntime sourceRun hsource
  have hsourceContinue :
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState .continue =
      some (.control (.continued sourceState.legacy.locals sourceState.legacy.globals
        sourceState.legacy.memory sourceState.legacy.ffi), sourceState.legacy.clock) := by
    simp [panToCrepSourceEvaluate, panSemEvaluateExactState, panSemEvaluate,
      panSemEvaluateWithFuel, panSemEvaluateFuel, PanSemExactState.toEvaluateState,
      evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  rw [hsourceContinue] at hsource
  injection hsource with hrun
  subst sourceRun
  cases fuel with
  | zero => omega
  | succ fuel =>
      refine ⟨((CrepRuntimeResult.continued 0 : CrepRuntimeResult α FfiFinalEvent),
        targetState), ?_, ?_⟩
      · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
          evalCrepRuntimeResult, evalCrepRuntimeProg]
      · simp [panToCrepRunResultRel, panToCrepControlResultRel, hclock]

/-- The `Annot` constructor is a no-op in the source and compiles to `Skip`,
so it has a concrete successful target run preserving the state and clock. -/
theorem panToCrepConcreteEvaluationGoal_annot
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ) (tag text : String)
    (hclock : sourceState.legacy.clock = targetState.clock)
    (hfuel : 0 < fuel) :
    panToCrepConcreteEvaluationGoal context sourceCode targetCode
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      fuel sourceState targetState (.annot tag text) := by
  intro _hruntime sourceRun hsource
  have hsourceAnnot :
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState (.annot tag text) =
      some (.control (.normal sourceState.legacy.locals sourceState.legacy.globals
        sourceState.legacy.memory sourceState.legacy.ffi), sourceState.legacy.clock) := by
    simp [panToCrepSourceEvaluate, panSemEvaluateExactState, panSemEvaluate,
      panSemEvaluateWithFuel, panSemEvaluateFuel, PanSemExactState.toEvaluateState,
      evalPanValueFfiClockProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  rw [hsourceAnnot] at hsource
  injection hsource with hrun
  subst sourceRun
  cases fuel with
  | zero => omega
  | succ fuel =>
      refine ⟨((CrepRuntimeResult.normal : CrepRuntimeResult α FfiFinalEvent),
        targetState), ?_, ?_⟩
      · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
          evalCrepRuntimeResult, evalCrepRuntimeProg]
      · simp [panToCrepRunResultRel, panToCrepControlResultRel, hclock]

/-- The `Tick` constructor preserves the concrete run relation across both
clock branches: zero-clock timeout and positive-clock decrement. -/
theorem panToCrepConcreteEvaluationGoal_tick
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceCode : FiniteMap FunName
      (List (VarName × Shape) × Prog α × Shape))
    (targetCode : FiniteMap FunName (List Nat × CrepProg α))
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α) (fuel : Nat)
    (sourceState : PanSemExactState α σ)
    (targetState : CrepRuntimeState α σ)
    (hclock : sourceState.legacy.clock = targetState.clock)
    (hfuel : 0 < fuel) :
    panToCrepConcreteEvaluationGoal context sourceCode targetCode
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      fuel sourceState targetState .tick := by
  intro _hruntime sourceRun hsource
  have hsourceTick :
      panToCrepSourceEvaluate sourceContext sourcePrimitive sourceHandler
        sourceState .tick =
      if sourceState.legacy.clock = 0 then
        some (panValueFfiClockTimeout sourceState.legacy.globals
          sourceState.legacy.memory sourceState.legacy.ffi sourceState.legacy.clock)
      else some (.control (.normal sourceState.legacy.locals sourceState.legacy.globals
        sourceState.legacy.memory sourceState.legacy.ffi),
        decPanClock sourceState.legacy.clock) := by
    simp [panToCrepSourceEvaluate, panSemEvaluateExactState, panSemEvaluate,
      panSemEvaluateWithFuel, panSemEvaluateFuel, PanSemExactState.toEvaluateState,
      evalPanValueFfiClockProg, panValueFfiClockTimeout]
  rw [hsourceTick] at hsource
  by_cases hzero : sourceState.legacy.clock = 0
  · simp [hzero, panValueFfiClockTimeout] at hsource
    cases hsource
    have htargetzero : targetState.clock = 0 := by
      rw [← hclock]
      exact hzero
    cases fuel with
    | zero => omega
    | succ fuel =>
        refine ⟨((CrepRuntimeResult.timeout : CrepRuntimeResult α FfiFinalEvent),
          clearCrepRuntimeLocals targetState), ?_, ?_⟩
        · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
            evalCrepRuntimeResult, evalCrepRuntimeProg, htargetzero]
        · simp [panToCrepRunResultRel, panToCrepControlResultRel,
            clearCrepRuntimeLocals, htargetzero]
  · simp [hzero] at hsource
    cases hsource
    have htargetNonzero : ¬targetState.clock = 0 := by
      intro htargetzero
      apply hzero
      calc
        sourceState.legacy.clock = targetState.clock := hclock
        _ = 0 := htargetzero
    cases fuel with
    | zero => omega
    | succ fuel =>
        refine ⟨((CrepRuntimeResult.normal : CrepRuntimeResult α FfiFinalEvent),
          decCrepClock targetState), ?_, ?_⟩
        · simp [panToCrepTargetEvaluate, compileCodeRelProg, compileProgHOL,
            evalCrepRuntimeResult, evalCrepRuntimeProg, htargetNonzero]
        · simp [panToCrepRunResultRel, panToCrepControlResultRel,
            decPanClock, decCrepClock, hclock]

end Flapjack
