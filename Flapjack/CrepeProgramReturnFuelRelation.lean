import Flapjack.CrepeReturnCorrectness

/-!
Fuel-polymorphic structured return correctness.

The base return theorem is stated at fuel one because it is convenient for
closed examples.  Program induction needs the same statement at arbitrary
positive source and Crep fuel, since a return can occur at any remaining
budget.
-/

namespace Flapjack

theorem compile_full_pan_value_return_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (expression : Exp α) (value : PanValue α)
    (compiled : List (CrepExp α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some value)
    (hvalid : panValuePayloadWithinLimit structs value = true)
    (hcompile : compileExp context expression =
      (compiled, panValueShape structs value))
    (hcompiled : evalCrepFullExps state.locals state.memory
      baseAddress topAddress compiled = some (panValueFlatWords value))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.return expression) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [value]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.return expression)) =
      some (.returned state (panValueFlatWords value)) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [value])
      (.returned state (panValueFlatWords value)) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · simp [compileProg, hcompile, evalCrepFullProg, hcompiled]
  · have hpost : panValueCrepStateRel structs context
        (fun _ => none) sourceGlobals sourceMemory state := by
      exact ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals,
        hrel.2.2⟩
    exact ⟨hpost, panValueCrepValuesRel_singleton value⟩

/-! Global-aware counterpart of the reusable return boundary.  The state
    relation currently targets localized source programs, so the only changed
    execution component is the evaluator carrying the separate Crep globals. -/
theorem compile_full_pan_value_return_state_relation_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
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
    (expression : Exp α) (value : PanValue α)
    (compiled : List (CrepExp α))
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hsource : evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
      baseAddress topAddress bytesInWord expression = some value)
    (hvalid : panValuePayloadWithinLimit structs value = true)
    (hcompile : compileExp context expression =
      (compiled, panValueShape structs value))
    (hcompiled : evalCrepFullExpsState state baseAddress topAddress compiled =
      some (panValueFlatWords value))
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory (.return expression) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [value]) ∧
    evalCrepFullProgState functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state
      (compileProg context (.return expression)) =
      some (.returned state (panValueFlatWords value)) ∧
    panValueCrepControlRel structs context exceptionRel
      (.returned (fun _ => none) sourceGlobals sourceMemory [value])
      (.returned state (panValueFlatWords value)) := by
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsource, hvalid]
  constructor
  · simp [compileProg, hcompile, evalCrepFullProgState, hcompiled]
  · have hpost : panValueCrepStateRel structs context
        (fun _ => none) sourceGlobals sourceMemory state := by
      exact ⟨hrel.1, panValueCrepLocalsRel_empty structs context state.locals,
        hrel.2.2⟩
    exact ⟨hpost, panValueCrepValuesRel_singleton value⟩

end Flapjack
