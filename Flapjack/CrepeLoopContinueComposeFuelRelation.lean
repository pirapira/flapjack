import Flapjack.CrepeStateRelation

/-!
Fuel-polymorphic composition for a nonzero loop whose body continues at
label zero.  Both evaluators consume the continue and re-enter the loop.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem compile_full_pan_value_while_continue_compose_fuel
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
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExp state.locals state.memory
      baseAddress topAddress compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
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
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel nextState
      (.while compiledCondition compiledBody) = some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition body)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceNonzero, hsourceBody, hsourceLoop]
  · simp [compileProg, hcompileCondition, hcompileBody,
      evalCrepFullProg, hcrepCondition, hconditionAgreement,
      hsourceNonzero, hcrepBody, hcrepLoop]

theorem compile_full_pan_value_while_continue_compose_state_fuel
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
    (condition : Exp α) (compiledCondition : CrepExp α)
    (body : Prog α) (compiledBody : CrepProg α)
    (sourceCondition targetCondition : α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (hcompileCondition : compileExp context condition =
      ([compiledCondition], .one))
    (hcompileBody : compileProg context body = compiledBody)
    (hsourceCondition : evalPanValueExp structs sourceLocals sourceGlobals
      sourceMemory baseAddress topAddress bytesInWord condition =
      some (.word sourceCondition))
    (hcrepCondition : evalCrepFullExpState state baseAddress topAddress
      compiledCondition = some targetCondition)
    (hconditionAgreement : targetCondition = sourceCondition)
    (hsourceNonzero : sourceCondition ≠ 0)
    (hsourceBody : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory body =
      some (.continued sourceNextLocals sourceNextGlobals sourceNextMemory))
    (hcrepBody : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state compiledBody =
      some (.continued nextState 0))
    (hsourceLoop : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceNextLocals sourceNextGlobals sourceNextMemory
      (.while condition body) = some sourceResult)
    (hcrepLoop : evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel nextState
      (.while compiledCondition compiledBody) = some crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.while condition body) =
      some sourceResult ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.while condition body)) = some crepResult := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceCondition,
      hsourceNonzero, hsourceBody, hsourceLoop]
  · simp [compileProg, hcompileCondition, hcompileBody,
      evalCrepFullProgState, hcrepCondition, hconditionAgreement,
      hsourceNonzero, hcrepBody, hcrepLoop]

end Flapjack
