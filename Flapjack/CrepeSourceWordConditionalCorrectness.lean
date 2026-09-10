import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeConditionalCorrectness

/-!
Connect structural source-word conditions to the relation-aware conditional
simulation rule.  Branch simulation remains an explicit induction hypothesis;
this theorem discharges the condition compilation and target agreement.
-/

namespace Flapjack

theorem compile_full_pan_value_ite_source_word_then_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (compiledThen compiledElse : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceThenResult : PanValueControlResult α)
    (crepThenResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition.toExp =
      some (.word sourceCondition))
    (hconditionAgreement : targetCondition = sourceCondition)
    (hnonzero : sourceCondition ≠ 0)
    (hcompileThen : compileProg context thenBranch = compiledThen)
    (hcompileElse : compileProg context elseBranch = compiledElse)
    (hsourceThen : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory thenBranch =
      some sourceThenResult)
    (hcrepThen : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledThen = some crepThenResult)
    (hthenRel : panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceThenResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepThenResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hnonzero' : (sourceCondition != 0) = true := by
    simpa using hnonzero
  exact compile_full_pan_value_ite_then_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord fuel condition.toExp
    compiledCondition thenBranch elseBranch compiledThen compiledElse sourceCondition
    targetCondition sourceThenResult crepThenResult exceptionRel hcompileCondition
    hcompileThen hcompileElse hsourceCondition hcrepCondition' hconditionAgreement
    hnonzero' hsourceThen hcrepThen hthenRel

theorem compile_full_pan_value_ite_source_word_else_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (condition : SourceWordExp α) (thenBranch elseBranch : Prog α)
    (compiledThen compiledElse : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceElseResult : PanValueControlResult α)
    (crepElseResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition.toExp =
      some (.word sourceCondition))
    (hconditionAgreement : targetCondition = sourceCondition)
    (hzero : sourceCondition = 0)
    (hcompileThen : compileProg context thenBranch = compiledThen)
    (hcompileElse : compileProg context elseBranch = compiledElse)
    (hsourceElse : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory elseBranch =
      some sourceElseResult)
    (hcrepElse : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledElse = some crepElseResult)
    (helseRel : panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceElseResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepElseResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hzero' : sourceCondition == 0 := by
    simpa using hzero
  exact compile_full_pan_value_ite_else_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord fuel condition.toExp
    compiledCondition thenBranch elseBranch compiledThen compiledElse sourceCondition
    targetCondition sourceElseResult crepElseResult exceptionRel hcompileCondition
    hcompileThen hcompileElse hsourceCondition hcrepCondition' hconditionAgreement
    hzero' hsourceElse hcrepElse helseRel

end Flapjack
