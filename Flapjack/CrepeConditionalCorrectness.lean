import Flapjack.CrepeStateRelation

/-!
Relation-aware conditional composition for the source-to-Crep simulation.
-/

namespace Flapjack

theorem compile_full_pan_value_ite_then_relation
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
    (thenBranch elseBranch : Prog α)
    (compiledThen compiledElse : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceThenResult : PanValueControlResult α)
    (crepThenResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileThen : compileProg context thenBranch = compiledThen)
    (hcompileElse : compileProg context elseBranch = compiledElse)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hnonzero : sourceCondition != 0)
    (hsourceThen : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory thenBranch =
      some sourceThenResult)
    (hcrepThen : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledThen =
      some crepThenResult)
    (hthenRel : panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition thenBranch elseBranch) = some sourceThenResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.ite condition thenBranch elseBranch)) =
      some crepThenResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult := by
  have hcompile : compileProg context (.ite condition thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hnonzero, hsourceThen]
  · constructor
    · simp [evalCrepFullProg, hcrepCondition, hconditionAgreement,
        hnonzero, hcrepThen]
    · exact hthenRel

theorem compile_full_pan_value_ite_else_relation
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
    (thenBranch elseBranch : Prog α)
    (compiledThen compiledElse : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceElseResult : PanValueControlResult α)
    (crepElseResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileThen : compileProg context thenBranch = compiledThen)
    (hcompileElse : compileProg context elseBranch = compiledElse)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hzero : sourceCondition == 0)
    (hsourceElse : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory elseBranch =
      some sourceElseResult)
    (hcrepElse : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledElse =
      some crepElseResult)
    (helseRel : panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition thenBranch elseBranch) = some sourceElseResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.ite condition thenBranch elseBranch)) =
      some crepElseResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult := by
  have hsourceZero : sourceCondition = 0 := by
    simpa using hzero
  have htargetZero : targetCondition = 0 := by
    simpa [hconditionAgreement] using hsourceZero
  have hcompile : compileProg context (.ite condition thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceZero, hsourceElse]
  · constructor
    · simp [evalCrepFullProg, hcrepCondition, htargetZero, hcrepElse]
    · exact helseRel

end Flapjack
