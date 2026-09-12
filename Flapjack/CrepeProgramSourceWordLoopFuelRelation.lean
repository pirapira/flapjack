import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeLoopComposeFuelRelation
import Flapjack.CrepeLoopBreakComposeFuelRelation
import Flapjack.CrepeLoopContinueComposeFuelRelation

/-!
Source-word condition bridge for the fuel-polymorphic normal-body loop rule.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_while_source_word_nonzero_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
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
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.normal nextState))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrepLoop : ∀ compiledCondition,
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel nextState
        (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.while condition.toExp body) = some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_nonzero_compose_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory sourceNextLocals sourceNextGlobals sourceNextMemory state nextState
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel condition.toExp compiledCondition body
    compiledBody sourceCondition targetCondition sourceResult crepResult
    hcompileCondition hcompileBody hsourceCondition hcrepCondition'
    hconditionAgreement hnonzero hsourceBody hcrepBody hsourceLoop
    (hcrepLoop compiledCondition)
  exact ⟨hresult.1, hresult.2, hloopRel⟩

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_while_source_word_break_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
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
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.broke sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.broke nextState 0))
    (hrel : panValueCrepStateRel structs context sourceNextLocals
      sourceNextGlobals sourceNextMemory nextState) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) =
      some (.normal nextState) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceNextLocals sourceNextGlobals sourceNextMemory)
      (.normal nextState) := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_break_compose_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory sourceNextLocals sourceNextGlobals sourceNextMemory state nextState
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel condition.toExp compiledCondition body
    compiledBody sourceCondition targetCondition hcompileCondition hcompileBody
    hsourceCondition hcrepCondition' hconditionAgreement hnonzero hsourceBody
    hcrepBody
  exact ⟨hresult.1, hresult.2,
    ⟨hrel.1, hrel.2.1, hrel.2.2⟩⟩

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_while_source_word_continue_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
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
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.continued sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.continued nextState 0))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrepLoop : ∀ compiledCondition,
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel nextState
        (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_continue_compose_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory sourceNextLocals sourceNextGlobals sourceNextMemory state nextState
    primitive sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
    bytesInWord sourceFuel targetFuel condition.toExp compiledCondition body
    compiledBody sourceCondition targetCondition sourceResult crepResult
    hcompileCondition hcompileBody hsourceCondition hcrepCondition'
    hconditionAgreement hnonzero hsourceBody hcrepBody hsourceLoop
    (hcrepLoop compiledCondition)
  exact ⟨hresult.1, hresult.2, hloopRel⟩

end Flapjack

namespace Flapjack

theorem compile_full_pan_value_while_source_word_break_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α) (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat) (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α) (sourceCondition targetCondition : α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord condition.toExp = some (.word sourceCondition))
    (hconditionAgreement : targetCondition = sourceCondition)
    (hnonzero : sourceCondition ≠ 0)
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.broke sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.broke nextState 0))
    (hrel : panValueCrepStateRel structs context sourceNextLocals sourceNextGlobals
      sourceNextMemory nextState) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) =
      some (.normal nextState) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceNextLocals sourceNextGlobals sourceNextMemory)
      (.normal nextState) := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_state_relation context structs sourceLocals sourceGlobals
      sourceMemory state baseAddress topAddress bytesInWord hbytesInWord
      hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_break_compose_state_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory state nextState primitive
    sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    sourceFuel targetFuel condition.toExp compiledCondition body compiledBody
    sourceCondition targetCondition hcompileCondition hcompileBody hsourceCondition
    hcrepCondition' hconditionAgreement hnonzero hsourceBody hcrepBody
  exact ⟨hresult.1, hresult.2, ⟨hrel.1, hrel.2.1, hrel.2.2⟩⟩

theorem compile_full_pan_value_while_source_word_continue_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α) (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat) (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α) (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α) (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hbytesInWord : context.bytesInWord = bytesInWord)
    (hlocals : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state)
    (hlookup : ∀ name value, sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord condition.toExp = some (.word sourceCondition))
    (hconditionAgreement : targetCondition = sourceCondition)
    (hnonzero : sourceCondition ≠ 0)
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.continued sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.continued nextState 0))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrepLoop : ∀ compiledCondition,
      evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel nextState
        (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_state_relation context structs sourceLocals sourceGlobals
      sourceMemory state baseAddress topAddress bytesInWord hbytesInWord
      hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_continue_compose_state_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory state nextState primitive
    sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    sourceFuel targetFuel condition.toExp compiledCondition body compiledBody
    sourceCondition targetCondition sourceResult crepResult hcompileCondition
    hcompileBody hsourceCondition hcrepCondition' hconditionAgreement hnonzero
    hsourceBody hcrepBody hsourceLoop (hcrepLoop compiledCondition)
  exact ⟨hresult.1, hresult.2, hloopRel⟩

end Flapjack

namespace Flapjack

/-! Stateful counterpart of the normal-body source-word loop bridge. -/

theorem compile_full_pan_value_while_source_word_nonzero_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceNextLocals sourceNextGlobals : VarName → Option (PanValue α))
    (sourceNextMemory : α → Option (PanValue α))
    (state nextState : CrepState α)
    (primitive : PanPrimitiveHandler α) (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (condition : SourceWordExp α) (body : Prog α)
    (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α) (crepResult : CrepControlResult α)
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
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody = some (.normal nextState))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler
      structs sourceFunctions baseAddress topAddress bytesInWord sourceFuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrepLoop : ∀ compiledCondition,
      evalCrepFullProgState functions crepPrimitive ffi sharedMem
        baseAddress topAddress targetFuel nextState
        (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi primitive sourceHandler structs
      sourceFunctions baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_state_relation context structs sourceLocals sourceGlobals
      sourceMemory state baseAddress topAddress bytesInWord hbytesInWord
      hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hresult := compile_full_pan_value_while_nonzero_compose_state_fuel
    context structs sourceFunctions functions sourceLocals sourceGlobals sourceMemory
    sourceNextLocals sourceNextGlobals sourceNextMemory state nextState primitive
    sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
    sourceFuel targetFuel condition.toExp compiledCondition body compiledBody
    sourceCondition targetCondition sourceResult crepResult hcompileCondition
    hcompileBody hsourceCondition hcrepCondition' hconditionAgreement hnonzero
    hsourceBody hcrepBody hsourceLoop (hcrepLoop compiledCondition)
  exact ⟨hresult.1, hresult.2, hloopRel⟩

end Flapjack
