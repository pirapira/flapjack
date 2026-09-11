import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeLoopCorrectness

/-!
Lift the structural source-word relation through the zero-condition loop
boundary.  The loop body is intentionally not evaluated in this case, as in
the source and Crep evaluators.
-/

namespace Flapjack

theorem compile_full_pan_value_while_source_word_zero_relation
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
    (condition : SourceWordExp α) (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α) (exceptionRel : ExceptionId → PanValue α → α → Prop)
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
    (hcompileBody : compileProg context body = compiledBody) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory
      (.while condition.toExp body) =
      some (.normal sourceLocals sourceGlobals sourceMemory) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition.toExp body)) =
      some (.normal state) ∧
    panValueCrepControlRel structs context exceptionRel
      (.normal sourceLocals sourceGlobals sourceMemory) (.normal state) := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  have hzero' : sourceCondition == 0 := by
    simpa using hzero
  exact compile_full_pan_value_while_zero_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord fuel condition.toExp
    compiledCondition body compiledBody sourceCondition targetCondition exceptionRel
    hcompileCondition hcompileBody hsourceCondition hcrepCondition' hconditionAgreement hzero'
    hlocals

theorem compile_full_pan_value_while_source_word_nonzero_relation
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
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (condition : SourceWordExp α) (body : Prog α) (compiledBody : CrepProg α)
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
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.normal sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress fuel state compiledBody =
      some (.normal nextState))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord fuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition.toExp body) = some sourceResult)
    (hcrepLoop : ∀ compiledCondition,
      evalCrepFullProg functions crepPrimitive ffi sharedMem
        baseAddress topAddress fuel nextState
        (.while compiledCondition compiledBody) = some crepResult)
    (hloopRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition.toExp body) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state
      (compileProg context (.while condition.toExp body)) = some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  obtain ⟨compiledCondition, hcompileCondition, hcrepCondition⟩ :=
    compileSourceWordExp_relation context structs sourceLocals sourceGlobals
      sourceMemory state.locals state.memory baseAddress topAddress bytesInWord
      hbytesInWord hlocals.2.1 hlookup condition sourceCondition hsourceCondition
  have hcrepCondition' : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition := by
    simpa [hconditionAgreement] using hcrepCondition
  exact compile_full_pan_value_while_nonzero_relation context structs sourceFunctions
    functions sourceLocals sourceGlobals sourceMemory sourceNextLocals
    sourceNextGlobals sourceNextMemory state nextState primitive sourceHandler
    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord fuel condition.toExp
    compiledCondition body compiledBody sourceCondition targetCondition sourceResult
    crepResult exceptionRel hcompileCondition hcompileBody hsourceCondition
    hcrepCondition' hconditionAgreement hnonzero hsourceBody hcrepBody hsourceLoop
    (hcrepLoop compiledCondition) hloopRel

end Flapjack
