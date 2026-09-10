import Flapjack.CrepeStateRelation

/-!
Relation-aware composition for normally completing statements.

This is the program-induction rule at the source-to-Crep boundary: the first
statement runs normally in both machines, and the continuation relation is
then preserved by the second-statement hypotheses.
-/

namespace Flapjack

theorem compile_full_pan_value_seq_normal_relation
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.normal sourceFirstLocals sourceFirstGlobals sourceFirstMemory))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state compiledFirst =
      some (.normal firstState))
    (hsourceSecond : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 1)
      sourceFirstLocals sourceFirstGlobals sourceFirstMemory second =
      some sourceResult)
    (hcrepSecond : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 1) firstState compiledSecond =
      some crepResult)
    (hsecondRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (fuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state
      (compileProg context (.seq first second)) =
      some crepResult ∧
    panValueCrepControlRel structs context exceptionRel sourceResult crepResult := by
  have hsequence := compile_full_pan_value_seq_normal_compose_full
    context structs sourceFunctions functions
    sourceLocals sourceGlobals sourceMemory
    sourceFirstLocals sourceFirstGlobals sourceFirstMemory
    state firstState primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord fuel first second
    compiledFirst compiledSecond sourceResult crepResult
    hcompileFirst hcompileSecond hsourceFirst hcrepFirst
    hsourceSecond hcrepSecond
  exact ⟨hsequence.1, hsequence.2, hsecondRel⟩

/-! The FFI lowering has a larger Crep fuel cost than its source step.  This
    mixed-fuel variant keeps the sequence rule usable when the first statement
    is an external call or another lowering with a fixed target overhead. -/
theorem compile_full_pan_value_seq_normal_relation_mixed_fuel
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α))
    (sourceFirstLocals sourceFirstGlobals : VarName → Option (PanValue α))
    (sourceFirstMemory : α → Option (PanValue α))
    (state firstState : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (first second : Prog α)
    (compiledFirst compiledSecond : CrepProg α)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (hcompileFirst : compileProg context first = compiledFirst)
    (hcompileSecond : compileProg context second = compiledSecond)
    (hsourceFirst : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceLocals sourceGlobals sourceMemory first =
      some (.normal sourceFirstLocals sourceFirstGlobals sourceFirstMemory))
    (hcrepFirst : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) state compiledFirst =
      some (.normal firstState))
    (hsourceSecond : evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 1)
      sourceFirstLocals sourceFirstGlobals sourceFirstMemory second =
      some sourceResult)
    (hcrepSecond : evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 1) firstState compiledSecond =
      some crepResult)
    (hsecondRel : panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult) :
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord (sourceFuel + 2)
      sourceLocals sourceGlobals sourceMemory (.seq first second) =
      some sourceResult ∧
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress (targetFuel + 2) state
      (compileProg context (.seq first second)) =
      some crepResult ∧
    panValueCrepControlRel structs context exceptionRel
      sourceResult crepResult := by
  have hcompile :
      compileProg context (.seq first second) =
        .seq compiledFirst compiledSecond := by
    simp [compileProg, hcompileFirst, hcompileSecond]
  rw [hcompile]
  constructor
  · simp [evalPanValueProgWithPrimitiveCallsAndFfi, hsourceFirst,
      hsourceSecond]
  · constructor
    · simp [evalCrepFullProg, hcrepFirst, hcrepSecond]
    · exact hsecondRel

end Flapjack
