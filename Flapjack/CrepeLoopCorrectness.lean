import Flapjack.CrepeStateRelation

/-!
Relation-aware loop composition for the source-to-Crep simulation.
-/

namespace Flapjack

theorem compile_full_pan_value_while_zero_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExpState state
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hzero : sourceCondition == 0)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some (.normal sourceLocals sourceGlobals sourceMemory) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) =
      some (.normal state) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal state) := by
  have hsourceZero : sourceCondition = 0 := by
    simpa using hzero
  have htargetZero : targetCondition = 0 := by
    simpa [hconditionAgreement] using hsourceZero
  have hcompile : compileProg context (.while condition body) =
      .while compiledCondition compiledBody := by
    simp [compileProg, hcompileCondition, hcompileBody]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceZero]
  · constructor
    · simp [evalCrepFullProgState, hcrepCondition, htargetZero]
    · exact hrel

theorem compile_full_pan_value_while_nonzero_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExpState state
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.normal nextState))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel nextState
      (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  have hresult := compile_full_pan_value_while_nonzero_compose
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory
    state nextState primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fuel condition compiledCondition body
    compiledBody sourceCondition targetCondition sourceResult crepResult
    hcompileCondition hcompileBody hsourceCondition hcrepCondition
    hconditionAgreement hsourceNonzero hsourceBody hcrepBody hsourceLoop hcrepLoop
  exact ⟨hresult.1, hresult.2, hloopRel⟩

theorem compile_full_pan_value_while_break_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExpState state
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.broke sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.broke nextState 0))
    (hrel : panValueCrepStateRel structs context sourceNextLocals
      sourceNextGlobals sourceNextMemory nextState) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) =
      some (.normal nextState) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceNextLocals sourceNextGlobals sourceNextMemory)
      (.normal nextState) := by
  have hresult := compile_full_pan_value_while_break_compose
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory
    state nextState primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fuel condition compiledCondition body
    compiledBody sourceCondition targetCondition hcompileCondition hcompileBody
    hsourceCondition hcrepCondition hconditionAgreement hsourceNonzero
    hsourceBody hcrepBody
  exact ⟨hresult.1, hresult.2, hrel⟩

theorem compile_full_pan_value_while_continue_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExpState state
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.continued sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.continued nextState 0))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel nextState
      (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  have hresult := compile_full_pan_value_while_continue_compose
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory
    state nextState primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fuel condition compiledCondition body
    compiledBody sourceCondition targetCondition sourceResult crepResult
    hcompileCondition hcompileBody hsourceCondition hcrepCondition
    hconditionAgreement hsourceNonzero hsourceBody hcrepBody hsourceLoop hcrepLoop
  exact ⟨hresult.1, hresult.2, hloopRel⟩

end Flapjack
