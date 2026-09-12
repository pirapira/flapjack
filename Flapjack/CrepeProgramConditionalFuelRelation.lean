import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeConditionalCorrectness

/-!
Fuel-polymorphic conditional source-to-Crep simulation.  The branch proof is
passed in as an induction hypothesis; this file supplies the condition
compilation and source/target branch-selection agreement.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_ite_source_word_then_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory thenBranch =
      some sourceThenResult)
    (hcrepThen : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledThen = some crepThenResult)
    (hthenRel : panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceThenResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
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
  have hcompile : compileProg context
      (.ite condition.toExp thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hnonzero', hsourceThen]
  constructor
  · simp [evalCrepFullProg, hcrepCondition', hconditionAgreement,
      hnonzero', hcrepThen]
  · exact hthenRel

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_ite_source_word_else_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory elseBranch =
      some sourceElseResult)
    (hcrepElse : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledElse = some crepElseResult)
    (helseRel : panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceElseResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepElseResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hsourceZero : sourceCondition = 0 := by
    simpa using hzero
  have htargetZero : targetCondition = 0 := by
    simpa [hconditionAgreement] using hsourceZero
  have hcompile : compileProg context
      (.ite condition.toExp thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceZero, hsourceElse]
  constructor
  · simp [evalCrepFullProg, hcrepCondition, hsourceZero, htargetZero,
      hcrepElse]
  · exact helseRel

/-! The same conditional composition for the global-aware Crep evaluator. -/
theorem compile_full_pan_value_ite_source_word_then_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory thenBranch =
      some sourceThenResult)
    (hcrepThen : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledThen = some crepThenResult)
    (hthenRel : panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceThenResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepThenResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceThenResult crepThenResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepConditionState : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition := by
    obtain ⟨compiledCondition', hcompileCondition', hnoGlobal⟩ :=
      compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord hlookup condition
        sourceCondition hsourceCondition
    have hcompiledEq : compiledCondition = compiledCondition' := by
      have hpair : ([compiledCondition], Shape.one) =
          ([compiledCondition'], Shape.one) :=
        hcompileCondition.symm.trans hcompileCondition'
      exact (List.cons.inj (congrArg Prod.fst hpair)).1
    have hcrepCondition' :
        evalCrepFullExp state.locals state.memory baseAddress topAddress
          compiledCondition' = some sourceCondition := by
      simpa [hcompiledEq] using hcrepCondition
    rw [hcompiledEq]
    rw [evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
      compiledCondition' hnoGlobal]
    simpa [hconditionAgreement] using hcrepCondition'
  have hcompile : compileProg context
      (.ite condition.toExp thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hnonzero, hsourceThen]
  constructor
  · simp [evalCrepFullProgState, hcrepConditionState,
      hconditionAgreement, hnonzero, hcrepThen]
  · exact hthenRel

theorem compile_full_pan_value_ite_source_word_else_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory elseBranch =
      some sourceElseResult)
    (hcrepElse : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledElse = some crepElseResult)
    (helseRel : panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.ite condition.toExp thenBranch elseBranch) = some sourceElseResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.ite condition.toExp thenBranch elseBranch)) =
      some crepElseResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceElseResult crepElseResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepConditionState : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition := by
    obtain ⟨compiledCondition', hcompileCondition', hnoGlobal⟩ :=
      compileSourceWordExp_noGlobal context structs sourceLocals sourceGlobals
        sourceMemory baseAddress topAddress bytesInWord hlookup condition
        sourceCondition hsourceCondition
    have hcompiledEq : compiledCondition = compiledCondition' := by
      have hpair : ([compiledCondition], Shape.one) =
          ([compiledCondition'], Shape.one) :=
        hcompileCondition.symm.trans hcompileCondition'
      exact (List.cons.inj (congrArg Prod.fst hpair)).1
    have hcrepCondition' :
        evalCrepFullExp state.locals state.memory baseAddress topAddress
          compiledCondition' = some sourceCondition := by
      simpa [hcompiledEq] using hcrepCondition
    rw [hcompiledEq]
    rw [evalCrepFullExpState_eq_of_noGlobal state baseAddress topAddress
      compiledCondition' hnoGlobal]
    simpa [hconditionAgreement] using hcrepCondition'
  have hcompile : compileProg context
      (.ite condition.toExp thenBranch elseBranch) =
      .ite compiledCondition compiledThen compiledElse := by
    simp [compileProg, hcompileCondition, hcompileThen, hcompileElse]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hzero, hsourceElse]
  constructor
  · simp [evalCrepFullProgState, hcrepConditionState,
      hconditionAgreement, hzero, hcrepElse]
  · exact helseRel

end Flapjack
