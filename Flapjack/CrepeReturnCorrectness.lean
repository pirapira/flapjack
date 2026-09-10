import Flapjack.CrepeStateRelation

/-!
Relation-aware correctness for a structured Pancake return.

The existing return equations compare the observable flattened result.  This
boundary keeps the structured source payload and, at the same time, exposes
the unchanged source-to-Crep state relation needed by program induction.
-/

namespace Flapjack

theorem compile_full_pan_value_return_relation
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
    (baseAddress topAddress bytesInWord : α)
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
      baseAddress topAddress bytesInWord 1
      sourceLocals sourceGlobals sourceMemory (.return expression) =
      some (.returned (fun _ => none) sourceGlobals sourceMemory [value]) ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress 1 state
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

end Flapjack
